#include <climits>
#include <cstring>
#include <cstdint>
#include <stdexcept>
#include <unordered_set>
#include <map>
#include <vector>
#include <set>
#include "ASTree.h"
#include "FastStack.h"
#include "pyc_numeric.h"
#include "bytecode.h"

// This must be a triple quote (''' or """), to handle interpolated string literals containing the opposite quote style.
// E.g. f'''{"interpolated "123' literal"}'''    -> valid.
// E.g. f"""{"interpolated "123' literal"}"""    -> valid.
// E.g. f'{"interpolated "123' literal"}'        -> invalid, unescaped quotes in literal.
// E.g. f'{"interpolated \"123\' literal"}'      -> invalid, f-string expression does not allow backslash.
// NOTE: Nested f-strings not supported.
#define F_STRING_QUOTE "'''"

static void append_to_chain_store(const PycRef<ASTNode>& chainStore,
        PycRef<ASTNode> item, FastStack& stack, const PycRef<ASTBlock>& curblock);
static bool ast_store_named_expr(PycRef<ASTNode> value, PycRef<ASTNode> name,
                                 FastStack& stack, PycModule* mod, bool wasDup,
                                 PycRef<PycCode> code, int pos);
static bool ast_keep_chain_target(PycRef<ASTNode> value, PycRef<ASTNode> target,
                                  FastStack& stack, PycModule* mod, bool wasDup);
static void ast_drop_named_dup(FastStack& stack, PycRef<PycCode> code, PycModule* mod, int pos);
static bool ast_is_yield_expr(PycRef<ASTNode> node);

/* Use this to determine if an error occurred (and therefore, if we should
 * avoid cleaning the output tree) */
static bool cleanBuild;

/* Use this to prevent printing return keywords and newlines in lambdas. */
static bool inLambda = false;

/* Use this to keep track of whether we need to print out any docstring and
 * the list of global variables that we are using (such as inside a function). */
static bool printDocstringAndGlobals = false;

/* Use this to keep track of whether we need to print a class or module docstring */
static bool printClassDocstring = true;

// Enclosing class names while printing class bodies, used to undo private name mangling
static std::vector<std::string> classNameStack;

static std::string unmangle_name(const char* name)
{
    std::string result(name);
    if (classNameStack.empty())
        return result;
    const std::string& cls = classNameStack.back();
    size_t start = cls.find_first_not_of('_');
    if (start == std::string::npos)
        return result;
    const std::string prefix = "_" + cls.substr(start) + "__";
    if (result.size() <= prefix.size() || result.compare(0, prefix.size(), prefix) != 0)
        return result;
    std::string original = result.substr(prefix.size() - 2);
    // Dunder and dotted names are never mangled
    if ((original.size() >= 4 && original.compare(original.size() - 2, 2, "__") == 0)
            || original.find('.') != std::string::npos)
        return result;
    return original;
}

// shortcut for all top/pop calls
static PycRef<ASTNode> StackPopTop(FastStack& stack)
{
    const auto node(stack.top());
    stack.pop();
    return node;
}

static bool ast_same_name(PycRef<ASTNode> left, PycRef<ASTNode> right)
{
    if (left == nullptr || right == nullptr
            || left.type() != ASTNode::NODE_NAME || right.type() != ASTNode::NODE_NAME)
        return false;
    PycRef<PycString> leftName = left.cast<ASTName>()->name();
    PycRef<PycString> rightName = right.cast<ASTName>()->name();
    return leftName != nullptr && rightName != nullptr
            && leftName->strValue() == rightName->strValue();
}

static PycRef<ASTNode> ast_condition_body(PycRef<ASTNode> cond, bool negative)
{
    return negative ? PycRef<ASTNode>(new ASTUnary(cond, ASTUnary::UN_NOT)) : cond;
}

static PycRef<ASTNode> ast_negate_condition(PycRef<ASTNode> cond)
{
    if (cond.type() == ASTNode::NODE_UNARY
            && cond.cast<ASTUnary>()->op() == ASTUnary::UN_NOT)
        return cond.cast<ASTUnary>()->operand();
    return new ASTUnary(cond, ASTUnary::UN_NOT);
}

static bool ast_attach_decorators(PycRef<ASTBlock> curblock,
        PycRef<ASTNode> value, PycRef<ASTNode> name)
{
    if (value == nullptr || value.type() != ASTNode::NODE_CALL
            || name == nullptr || name.type() != ASTNode::NODE_NAME
            || curblock == nullptr || curblock->nodes().empty())
        return false;

    PycRef<ASTNode> previous = curblock->nodes().back();
    if (previous.type() != ASTNode::NODE_STORE)
        return false;
    PycRef<ASTNode> definition = previous.cast<ASTStore>()->src();
    if ((definition.type() != ASTNode::NODE_FUNCTION && definition.type() != ASTNode::NODE_CLASS)
            || !ast_same_name(previous.cast<ASTStore>()->dest(), name))
        return false;

    if (definition.type() == ASTNode::NODE_FUNCTION) {
        PycRef<PycCode> functionCode = definition.cast<ASTFunction>()->code()
                .cast<ASTObject>()->object().cast<PycCode>();
        if (functionCode->name()->isEqual("<lambda>"))
            return false;
    }

    std::vector<PycRef<ASTNode>> decorators;
    PycRef<ASTNode> callNode = value;
    while (callNode.type() == ASTNode::NODE_CALL) {
        PycRef<ASTCall> call = callNode.cast<ASTCall>();
        if (call->pparams().size() != 1 || !call->kwparams().empty())
            return false;
        decorators.push_back(call->func());
        callNode = call->pparams().front();
    }
    if (!ast_same_name(callNode, name))
        return false;

    for (const auto& decorator : decorators) {
        if (definition.type() == ASTNode::NODE_FUNCTION)
            definition.cast<ASTFunction>()->addDecorator(decorator);
        else
            definition.cast<ASTClass>()->addDecorator(decorator);
    }
    return true;
}

// Rebuild __build_class__(func, name, *bases, **kw) from the top npos stack args into an ASTClass
static bool ast_try_build_class(FastStack& stack, PycModule* mod, int npos,
                                const ASTCall::kwparam_t& classKw)
{
    if (npos < 2)
        return false;

    FastStack trial = stack;
    ASTTuple::value_t bases(npos - 2);
    for (int i = npos - 3; i >= 0; --i) {
        bases[i] = trial.top();
        trial.pop();
        if (bases[i] == nullptr)
            return false;
    }
    PycRef<ASTNode> name = trial.top();
    trial.pop();
    PycRef<ASTNode> function = trial.top();
    trial.pop();
    PycRef<ASTNode> loadbuild = trial.top();
    trial.pop();
    // 3.13+ pushes the NULL after LOAD_BUILD_CLASS
    if (mod->verCompare(3, 13) >= 0 && loadbuild == nullptr && !trial.empty()) {
        loadbuild = trial.top();
        trial.pop();
    }
    if (loadbuild.type() != ASTNode::NODE_LOADBUILDCLASS)
        return false;
    // Drop the 3.11/3.12 NULL below LOAD_BUILD_CLASS so a decorator call sees its real callable
    if (mod->verCompare(3, 11) >= 0 && !trial.empty() && trial.top() == nullptr)
        trial.pop();

    stack = trial;
    PycRef<ASTNode> call = new ASTCall(function, ASTCall::pparam_t(), classKw);
    stack.push(new ASTClass(call, new ASTTuple(bases), name));
    return true;
}

// Keyword-name tuple consumed by CALL_KW / CALL_FUNCTION_KW (3.6+)
static PycRef<PycSimpleSequence> ast_kw_names_tuple(PycRef<ASTNode> node)
{
    PycRef<ASTObject> obj = node.try_cast<ASTObject>();
    if (obj == nullptr || (obj->object().type() != PycObject::TYPE_TUPLE
            && obj->object().type() != PycObject::TYPE_SMALL_TUPLE))
        return nullptr;
    return obj->object().cast<PycSimpleSequence>();
}

static int ast_relative_jump_target(PycModule* mod, int opcode, int operand, int pos, bool backward);

// 3.8-3.11 break: forward jump to the innermost for loop's exit, or past its else clause (elseEnd is then set)
static bool ast_is_for_exit_jump(std::stack<PycRef<ASTBlock> > blocks, int from, int target,
                                 PycRef<PycCode> code, PycModule* mod, int& elseEnd)
{
    elseEnd = 0;
    while (!blocks.empty()) {
        PycRef<ASTBlock> blk = blocks.top();
        if (blk->blktype() == ASTBlock::BLK_FOR) {
            if (blk.cast<ASTIterBlock>()->isComprehension() || target < blk->end()
                    || from >= blk->end())
                return false;
            if (target == blk->end())
                return true;
            // Past the exit: a threaded break when the exit itself jumps there, otherwise it skips the for-else body
            PycBuffer peek(code->code()->value(), code->code()->length());
            int op = 0, arg = 0, after = blk->end();
            if (!peek.setPos(blk->end()))
                return false;
            bc_next(peek, mod, op, arg, after);
            int jumpTarget = -1;
            if (op == Pyc::JUMP_FORWARD_A)
                jumpTarget = ast_relative_jump_target(mod, op, arg, after, false);
            else if (op == Pyc::JUMP_ABSOLUTE_A)
                jumpTarget = mod->verCompare(3, 10) >= 0 ? arg * (int)sizeof(uint16_t) : arg;
            if (jumpTarget != target)
                elseEnd = target;
            return true;
        }
        if (blk->blktype() == ASTBlock::BLK_WHILE || blk->blktype() == ASTBlock::BLK_ASYNCFOR)
            return false;
        blocks.pop();
    }
    return false;
}

// Innermost open for loop, used to attach a for-else end found at a break
// Forward jump from inside a while body to (or past) that loop's exit: a break (3.8+ has no BREAK_LOOP)
static bool ast_is_while_exit_jump(std::stack<PycRef<ASTBlock> > blocks, int target)
{
    while (!blocks.empty()) {
        int bt = blocks.top()->blktype();
        if (bt == ASTBlock::BLK_FOR || bt == ASTBlock::BLK_ASYNCFOR)
            return false;
        if (bt == ASTBlock::BLK_WHILE)
            return blocks.top()->end() > 0 && target >= blocks.top()->end();
        blocks.pop();
    }
    return false;
}

static PycRef<ASTBlock> ast_innermost_for(std::stack<PycRef<ASTBlock> > blocks)
{
    while (!blocks.empty() && blocks.top()->blktype() != ASTBlock::BLK_FOR)
        blocks.pop();
    return blocks.empty() ? PycRef<ASTBlock>() : blocks.top();
}

// Emit break; close enclosing ifs whose false branch jumps back to the loop head (pre-3.11)
// Break right after a just-closed try body (iterator POP_TOP at its end) ends that try body
static PycRef<ASTBlock> ast_break_dest(PycRef<ASTBlock> curblock, int curpos)
{
    PycRef<ASTBlock> dest = curblock;
    if (!curblock->nodes().empty() && curblock->nodes().back().type() == ASTNode::NODE_BLOCK
            && curblock->nodes().back().cast<ASTBlock>()->blktype() == ASTBlock::BLK_CONTAINER) {
        for (const auto& child : curblock->nodes().back().cast<ASTBlock>()->nodes()) {
            if (child.type() == ASTNode::NODE_BLOCK && child.cast<ASTBlock>()->blktype() == ASTBlock::BLK_TRY
                    && child.cast<ASTBlock>()->end() >= curpos - 2 && child.cast<ASTBlock>()->end() <= curpos)
                dest = child.cast<ASTBlock>();
        }
    }
    return dest;
}

// Pending short-circuit at one target: a repeated operator folds left (`a or b or c`), a different one nests
static void ast_push_short_circuit(std::vector<ASTBinary::BinOp>& pending, ASTBinary::BinOp op, FastStack& stack)
{
    if (!pending.empty() && pending.back() == op && stack.size() >= 2) {
        PycRef<ASTNode> right = stack.top();
        stack.pop();
        PycRef<ASTNode> left = stack.top();
        stack.pop();
        stack.push(new ASTBinary(left, right, op));
        return;
    }
    pending.push_back(op);
}

static void ast_emit_for_break(std::stack<PycRef<ASTBlock> >& blocks, PycRef<ASTBlock>& curblock,
                               FastStack& stack, stackhist_t& stack_hist, int curpos)
{
    ast_break_dest(curblock, curpos)->append(new ASTKeyword(ASTKeyword::KW_BREAK));
    while (blocks.size() > 1 && curblock->end() <= curpos
            && (curblock->blktype() == ASTBlock::BLK_IF
                || curblock->blktype() == ASTBlock::BLK_ELIF
                || curblock->blktype() == ASTBlock::BLK_ELSE)) {
        PycRef<ASTBlock> done = curblock;
        blocks.pop();
        curblock = blocks.top();
        curblock->append(done.cast<ASTNode>());
        if (!stack_hist.empty()) {
            stack = stack_hist.top();
            stack_hist.pop();
        }
    }
}

// Elements of a starred-unpack operand: tuple/list displays and const tuples expand, anything else becomes *item
static void ast_append_unpacked(std::vector<PycRef<ASTNode> >& out, PycRef<ASTNode> item)
{
    if (item.type() == ASTNode::NODE_TUPLE) {
        for (const auto& v : item.cast<ASTTuple>()->values())
            out.push_back(v);
    } else if (item.type() == ASTNode::NODE_LIST) {
        for (const auto& v : item.cast<ASTList>()->values())
            out.push_back(v);
    } else if (item.type() == ASTNode::NODE_OBJECT
            && (item.cast<ASTObject>()->object().type() == PycObject::TYPE_TUPLE
                || item.cast<ASTObject>()->object().type() == PycObject::TYPE_SMALL_TUPLE)) {
        for (const auto& v : item.cast<ASTObject>()->object().cast<PycTuple>()->values())
            out.push_back(new ASTObject(v));
    } else {
        out.push_back(new ASTUnary(item, ASTUnary::UN_STAR));
    }
}

// Merge a mapping operand into map: dict displays and const-key maps copy entries, anything else becomes **item
static void ast_merge_mapping(PycRef<ASTMap> map, PycRef<ASTNode> item)
{
    if (item.type() == ASTNode::NODE_MAP) {
        for (const auto& kv : item.cast<ASTMap>()->values())
            map->add(kv.first, kv.second);
    } else if (item.type() == ASTNode::NODE_CONST_MAP) {
        PycRef<ASTConstMap> cm = item.cast<ASTConstMap>();
        PycRef<ASTObject> keys = cm->keys().try_cast<ASTObject>();
        PycRef<PycSimpleSequence> keySeq;
        if (keys != nullptr)
            keySeq = keys->object().try_cast<PycSimpleSequence>();
        if (keySeq == nullptr || keySeq->values().size() != cm->values().size()) {
            map->add(nullptr, item);
            return;
        }
        auto val = cm->values().cbegin();
        for (const auto& key : keySeq->values())
            map->add(new ASTObject(key), *val++);
    } else {
        map->add(nullptr, item);
    }
}

static bool ast_read_wordcode_instr(PycRef<PycString> bytes, PycModule* mod,
                                    int offset, int& opcode, int& operand, int& next);

// 3.12+: if the code at `from` repeats the loop-exit code (after END_FOR and the iterator pop) up to its return,
// return the offset after that copy, else -1; a copy of only a later part of it means the skipped part is a
// for-else body, whose end is stored in elseEnd
static int ast_duplicated_loop_exit(PycRef<PycCode> code, PycModule* mod, int from, int loopEnd, int& elseEnd)
{
    elseEnd = 0;
    auto next = [&](int& at, int& op, int& arg) {
        int after = 0;
        do {
            if (!ast_read_wordcode_instr(code->code(), mod, at, op, arg, after))
                return false;
            at = after;
        } while (op == Pyc::CACHE || op == Pyc::NOT_TAKEN);
        return true;
    };
    auto norm = [](int op) {
        if (op == Pyc::LOAD_FAST_BORROW_A || op == Pyc::LOAD_FAST_CHECK_A)
            return (int)Pyc::LOAD_FAST_A;
        if (op == Pyc::LOAD_FAST_BORROW_LOAD_FAST_BORROW_A)
            return (int)Pyc::LOAD_FAST_LOAD_FAST_A;
        return op;
    };
    int exitAt = loopEnd, op = 0, arg = 0;
    if (!next(exitAt, op, arg) || (op != Pyc::END_FOR && op != Pyc::INSTRUMENTED_END_FOR_A))
        return -1;
    int afterEnd = exitAt;
    if (next(afterEnd, op, arg) && (op == Pyc::POP_TOP || op == Pyc::POP_ITER))
        exitAt = afterEnd;
    if (from >= loopEnd)
        return -1;
    auto matchFrom = [&](int exitStart) {
        int at = from, ex = exitStart;
        for (int steps = 0; steps < 48; steps++) {
            int op1 = 0, arg1 = 0, op2 = 0, arg2 = 0;
            if (!next(at, op1, arg1) || !next(ex, op2, arg2) || norm(op1) != norm(op2) || arg1 != arg2)
                return -1;
            if (op1 == Pyc::RETURN_VALUE || op1 == Pyc::RETURN_CONST_A)
                return at;
            if (op1 == Pyc::JUMP_FORWARD_A || op1 == Pyc::JUMP_BACKWARD_A || op1 == Pyc::POP_JUMP_IF_FALSE_A
                    || op1 == Pyc::POP_JUMP_IF_TRUE_A || op1 == Pyc::FOR_ITER_A || op1 == Pyc::RAISE_VARARGS_A)
                return -1;
        }
        return -1;
    };
    int start = exitAt;
    for (int steps = 0; steps < 48; steps++) {
        int copyEnd = matchFrom(start);
        if (copyEnd > 0) {
            if (start != exitAt)
                elseEnd = start;
            return copyEnd;
        }
        int probe = start;
        if (!next(probe, op, arg) || op == Pyc::RETURN_VALUE || op == Pyc::RETURN_CONST_A
                || op == Pyc::JUMP_FORWARD_A || op == Pyc::JUMP_BACKWARD_A)
            break;
        start = probe;
    }
    return -1;
}

static bool ast_is_decorator_target(PycRef<ASTNode> node)
{
    return node.type() == ASTNode::NODE_FUNCTION
            || node.type() == ASTNode::NODE_CLASS
            || (node.type() == ASTNode::NODE_CALL
                && node.cast<ASTCall>()->isDecorator());
}

// Function/class passed straight to a call is a decorator target: emit it and pass its name
static PycRef<ASTNode> ast_decorated_definition_name(PycRef<ASTBlock> curblock,
                                                     PycRef<ASTNode> target)
{
    PycRef<PycString> name;
    if (target.type() == ASTNode::NODE_FUNCTION) {
        name = target.cast<ASTFunction>()->code().cast<ASTObject>()->object()
                .cast<PycCode>()->name();
        if (name->isEqual("<lambda>"))
            return target;
    } else if (target.type() == ASTNode::NODE_CLASS) {
        PycRef<ASTNode> cname = target.cast<ASTClass>()->name();
        if (cname.type() == ASTNode::NODE_NAME)
            name = cname.cast<ASTName>()->name();
        else if (cname.type() == ASTNode::NODE_OBJECT)
            name = cname.cast<ASTObject>()->object().try_cast<PycString>();
    }
    if (name == nullptr)
        return target;
    PycRef<ASTNode> decor_name = new ASTName(name);
    curblock->append(new ASTStore(target, decor_name));
    return decor_name;
}

// Add a target to the pending unpack tuple; emit the assignment once all targets are present
static bool ast_add_unpack_target(PycRef<ASTNode> name, int& unpack, int unpackStar,
                                  FastStack& stack, PycRef<ASTBlock> curblock)
{
    PycRef<ASTTuple> tup = stack.top().try_cast<ASTTuple>();
    if (tup == nullptr)
        return false;
    if (unpack == unpackStar)
        name = new ASTUnary(name, ASTUnary::UN_STAR);
    tup->add(name);

    if (--unpack <= 0) {
        if (unpackStar >= 0)
            tup->setRequireParens(false);
        stack.pop();
        PycRef<ASTNode> seq = stack.top();
        stack.pop();

        if (curblock->blktype() == ASTBlock::BLK_FOR && !curblock->inited()) {
            tup->setRequireParens(false);
            curblock.cast<ASTIterBlock>()->setIndex(tup.cast<ASTNode>());
        } else if (seq.type() == ASTNode::NODE_CHAINSTORE) {
            append_to_chain_store(seq, tup.cast<ASTNode>(), stack, curblock);
        } else {
            curblock->append(new ASTStore(seq, tup.cast<ASTNode>()));
        }
    }
    return true;
}

static int ast_inline_cache_entries(PycModule* mod, int opcode)
{
    if (mod->verCompare(3, 11) < 0)
        return 0;

    switch (opcode) {
    case Pyc::BINARY_OP_A:
        return mod->verCompare(3, 14) >= 0 ? 5 : 1;
    case Pyc::CALL_A:
    case Pyc::CALL_KW_A:
    case Pyc::LOAD_GLOBAL_A:
        return mod->verCompare(3, 14) >= 0 ? 4 : 0;
    case Pyc::LOAD_ATTR_A:
        return mod->verCompare(3, 14) >= 0 ? 9 : 0;
    case Pyc::STORE_ATTR_A:
        return mod->verCompare(3, 14) >= 0 ? 4 : 0;
    case Pyc::TO_BOOL:
        return mod->verCompare(3, 14) >= 0 ? 3 : 0;
    case Pyc::COMPARE_OP_A:
    case Pyc::CONTAINS_OP_A:
    case Pyc::FOR_ITER_A:
    case Pyc::INSTRUMENTED_FOR_ITER_A:
    case Pyc::SEND_A:
    case Pyc::STORE_SUBSCR:
        return 1;
    case Pyc::JUMP_BACKWARD_A:
    case Pyc::JUMP_BACKWARD_NO_INTERRUPT_A:
    case Pyc::INSTRUMENTED_JUMP_BACKWARD_A:
    case Pyc::POP_JUMP_IF_FALSE_A:
    case Pyc::POP_JUMP_IF_TRUE_A:
    case Pyc::POP_JUMP_IF_NONE_A:
    case Pyc::POP_JUMP_IF_NOT_NONE_A:
    case Pyc::INSTRUMENTED_POP_JUMP_IF_FALSE_A:
    case Pyc::INSTRUMENTED_POP_JUMP_IF_TRUE_A:
    case Pyc::INSTRUMENTED_POP_JUMP_IF_NONE_A:
    case Pyc::INSTRUMENTED_POP_JUMP_IF_NOT_NONE_A:
        return mod->verCompare(3, 13) >= 0 ? 1 : 0;
    default:
        return 0;
    }
}

static int ast_next_instr_offset_after_caches(PycModule* mod, int opcode, int pos)
{
    return pos + ast_inline_cache_entries(mod, opcode) * (int)sizeof(uint16_t);
}

static int ast_relative_jump_target(PycModule* mod, int opcode, int operand, int pos, bool backward)
{
    int offs = operand;
    if (mod->verCompare(3, 10) >= 0)
        offs *= sizeof(uint16_t);

    int base = pos;
    if (mod->verCompare(3, 12) >= 0)
        base = ast_next_instr_offset_after_caches(mod, opcode, pos);

    return backward ? base - offs : base + offs;
}

// Pre-3.11: whether the try whose handler starts at `handler` is the last statement of the loop starting at `loopStart`
static bool ast_pre311_try_is_loop_tail(PycRef<PycCode> code, PycModule* mod, int handler, int loopStart,
                                        const std::stack<PycRef<ASTBlock> >& blocks)
{
    if (mod->verCompare(3, 11) >= 0 || handler <= 0)
        return false;
    int loopEnd = 0;
    std::stack<PycRef<ASTBlock> > pending = blocks;
    while (!pending.empty() && !loopEnd) {
        if (pending.top()->blktype() == ASTBlock::BLK_FOR || pending.top()->blktype() == ASTBlock::BLK_ASYNCFOR
                || pending.top()->blktype() == ASTBlock::BLK_WHILE)
            loopEnd = pending.top()->end();
        pending.pop();
    }
    int op = 0, arg = 0, next = 0;
    // Final back-edge of the body: right before the loop exit (3.7: before its POP_BLOCK)
    int last = loopEnd - 2;
    if (last > 0 && ast_read_wordcode_instr(code->code(), mod, last, op, arg, next) && op == Pyc::POP_BLOCK)
        last -= 2;
    if (last <= handler || !ast_read_wordcode_instr(code->code(), mod, last, op, arg, next)
            || op != Pyc::JUMP_ABSOLUTE_A || (mod->verCompare(3, 10) >= 0 ? arg * 2 : arg) != loopStart)
        return false;
    // The handler's own END_FINALLY/RERAISE (nested setups balanced) must end right before it
    int depth = 0;
    for (int at = handler; at < last && ast_read_wordcode_instr(code->code(), mod, at, op, arg, next); at = next) {
        if (op == Pyc::SETUP_FINALLY_A || op == Pyc::SETUP_EXCEPT_A || op == Pyc::SETUP_WITH_A
                || op == Pyc::SETUP_ASYNC_WITH_A)
            depth++;
        else if (op == Pyc::END_FINALLY || op == Pyc::RERAISE || op == Pyc::RERAISE_A) {
            if (depth == 0)
                return next == last;
            depth--;
        }
    }
    return false;
}

// Whether a 3.11 handler starting at `handler` jumps forward to code after the try that is still inside the loop
static bool ast_handler_resumes_in_loop(PycRef<PycCode> code, PycModule* mod,
                                        const std::vector<PycExceptionTableEntry>& entries, int handler, int loopEnd)
{
    int cleanup = -1;
    for (const auto& entry : entries) {
        if (entry.push_lasti && entry.start_offset == handler)
            cleanup = entry.target;
    }
    int op = 0, arg = 0, next = 0;
    for (int at = handler; at < cleanup && ast_read_wordcode_instr(code->code(), mod, at, op, arg, next); at = next) {
        if (op != Pyc::JUMP_FORWARD_A)
            continue;
        int target = ast_relative_jump_target(mod, op, arg, next, false);
        if (target >= cleanup && (loopEnd <= 0 || target < loopEnd))
            return true;
    }
    return cleanup < 0;
}

// 3.12+ loop whose after-try code was placed at `fragment`, behind the handler starting at `handler`
static PycRef<ASTBlock> ast_loop_of_handler_fragment(PycRef<PycCode> code, PycModule* mod,
                                                      const std::vector<PycExceptionTableEntry>& entries, int handler,
                                                      int fragment, const std::map<int, PycRef<ASTBlock> >& forBlockAt)
{
    int tryStart = -1;
    for (const auto& entry : entries) {
        if (entry.target == handler && (tryStart < 0 || entry.start_offset < tryStart))
            tryStart = entry.start_offset;
    }
    PycRef<ASTBlock> loop;
    for (const auto& f : forBlockAt) {
        if (f.first < tryStart && tryStart < f.second->end())
            loop = f.second;
    }
    if (loop == nullptr || fragment <= handler || fragment <= loop->end())
        return PycRef<ASTBlock>();
    // The fragment must run back to the loop head before the next handler
    int op = 0, arg = 0, next = 0;
    for (int at = fragment; ast_read_wordcode_instr(code->code(), mod, at, op, arg, next); at = next) {
        if (op == Pyc::PUSH_EXC_INFO)
            break;
        if ((op == Pyc::JUMP_BACKWARD_A || op == Pyc::JUMP_BACKWARD_NO_INTERRUPT_A)
                && ast_relative_jump_target(mod, op, arg, next, true) == loop.cast<ASTIterBlock>()->start())
            return loop;
    }
    return PycRef<ASTBlock>();
}

// Try body of a try/except statement ending `blk`
static PycRef<ASTBlock> ast_last_try_body(PycRef<ASTBlock> blk)
{
    if (blk->nodes().empty() || blk->nodes().back().type() != ASTNode::NODE_BLOCK
            || blk->nodes().back().cast<ASTBlock>()->blktype() != ASTBlock::BLK_CONTAINER
            || !blk->nodes().back().cast<ASTContainerBlock>()->hasExcept())
        return PycRef<ASTBlock>();
    for (const auto& child : blk->nodes().back().cast<ASTBlock>()->nodes()) {
        if (child.type() == ASTNode::NODE_BLOCK && child.cast<ASTBlock>()->blktype() == ASTBlock::BLK_TRY)
            return child.cast<ASTBlock>();
    }
    return PycRef<ASTBlock>();
}

// Whether the handler at `handler` resumes in after-try code of `loop` placed behind the handler (3.12+)
static bool ast_handler_exits_to_fragment(PycRef<PycCode> code, PycModule* mod,
                                          const std::vector<PycExceptionTableEntry>& entries, int handler,
                                          const std::map<int, PycRef<ASTBlock> >& forBlockAt, PycRef<ASTBlock> loop)
{
    int cleanup = -1;
    for (const auto& entry : entries) {
        if (entry.push_lasti && entry.start_offset == handler)
            cleanup = entry.target;
    }
    int op = 0, arg = 0, next = 0;
    for (int at = handler; at < cleanup && ast_read_wordcode_instr(code->code(), mod, at, op, arg, next); at = next) {
        if (op != Pyc::JUMP_FORWARD_A)
            continue;
        int target = ast_relative_jump_target(mod, op, arg, next, false);
        if (target > cleanup && ast_loop_of_handler_fragment(code, mod, entries, handler, target, forBlockAt) == loop)
            return true;
    }
    return false;
}

// Whether real loop-body code follows a try whose handler starts at `handler` (its exit is neither the back-edge nor the loop exit)
static bool ast_is_synthetic_exception_cleanup(PycRef<PycCode> code, PycModule* mod, int offset, int& end);

static bool ast_code_follows_try(PycRef<PycCode> code, PycModule* mod,
                                 const std::vector<PycExceptionTableEntry>& entries, int handler,
                                 int loopStart, const std::stack<PycRef<ASTBlock> >& blocks)
{
    int at = -1;
    for (const auto& entry : entries) {
        if (entry.target == handler && entry.end_offset > at)
            at = entry.end_offset;
    }
    int loopEnd = 0;
    std::stack<PycRef<ASTBlock> > pending = blocks;
    while (!pending.empty() && !loopEnd) {
        int bt = pending.top()->blktype();
        if (bt == ASTBlock::BLK_FOR || bt == ASTBlock::BLK_ASYNCFOR || bt == ASTBlock::BLK_WHILE)
            loopEnd = pending.top()->end();
        pending.pop();
    }
    int op = 0, arg = 0, next = 0;
    // Loop already closed (handler decoded out of line): its FOR_ITER gives the exit
    if (loopEnd <= 0 && ast_read_wordcode_instr(code->code(), mod, loopStart, op, arg, next) && op == Pyc::FOR_ITER_A)
        loopEnd = ast_relative_jump_target(mod, op, arg, next, false);
    // Only in-line code between the loop exit and the first handler behind it leaves the loop
    int outOfLine = handler;
    for (const auto& entry : entries) {
        if (loopEnd > 0 && entry.target >= loopEnd && entry.target < outOfLine)
            outOfLine = entry.target;
    }
    for (int hops = 0; at >= 0 && hops < 4; hops++) {
        while (ast_read_wordcode_instr(code->code(), mod, at, op, arg, next)
                && (op == Pyc::CACHE || op == Pyc::NOP))
            at = next;
        if ((hops == 0 && at >= handler) || (loopEnd > 0 && at >= loopEnd && at < outOfLine))
            return false;
        if (op == Pyc::JUMP_FORWARD_A) {
            at = ast_relative_jump_target(mod, op, arg, next, false);
            continue;
        }
        // break compiled as the iterator POP_TOP plus a copy of the after-loop code (3.12+)
        int dupElse = 0, from = next, op2 = 0, arg2 = 0, next2 = 0;
        // 3.15 pops the two-slot iterator with a POP_TOP pair
        if (op == Pyc::POP_TOP && mod->verCompare(3, 15) >= 0
                && ast_read_wordcode_instr(code->code(), mod, from, op2, arg2, next2) && op2 == Pyc::POP_TOP)
            from = next2;
        int copyEnd = op == Pyc::POP_TOP && loopEnd > 0 ? ast_duplicated_loop_exit(code, mod, from, loopEnd, dupElse) : -1;
        if (copyEnd > from) {
            at = copyEnd;
            continue;
        }
        // Try body ending in a return or break: its unprotected iterator cleanup is skipped, the code after it decides
        // (also an enclosing handler's POP_EXCEPT and `as name` cleanup when this try ends that handler)
        int r = at, cleanupEnd = 0;
        bool leavesHandler = false;
        while (ast_read_wordcode_instr(code->code(), mod, r, op, arg, next)) {
            if (ast_is_synthetic_exception_cleanup(code, mod, r, cleanupEnd)) {
                leavesHandler = true;
                r = cleanupEnd;
                continue;
            }
            if (op != Pyc::CACHE && op != Pyc::SWAP_A && op != Pyc::POP_TOP && op != Pyc::POP_EXCEPT
                    && op != Pyc::LOAD_CONST_A && op != Pyc::LOAD_SMALL_INT_A && op != Pyc::LOAD_COMMON_CONSTANT_A)
                break;
            leavesHandler = leavesHandler || op == Pyc::POP_EXCEPT;
            r = next;
        }
        if ((op == Pyc::JUMP_BACKWARD_A || op == Pyc::JUMP_BACKWARD_NO_INTERRUPT_A)
                && ast_relative_jump_target(mod, op, arg, next, true) == loopStart)
            return false;
        // A return after leaving the enclosing handler is decoded as a statement after this try
        if (leavesHandler)
            return true;
        bool exitsLoop = op == Pyc::JUMP_FORWARD_A && loopEnd > 0
                && ast_relative_jump_target(mod, op, arg, next, false) >= loopEnd;
        if (op != Pyc::RETURN_VALUE && op != Pyc::RETURN_CONST_A && !exitsLoop) {
            ast_read_wordcode_instr(code->code(), mod, at, op, arg, next);
            break;
        }
        at = next;
    }
    if (at < 0 || op == Pyc::JUMP_FORWARD_A || op == Pyc::END_FOR || op == Pyc::INSTRUMENTED_END_FOR_A
            || op == Pyc::PUSH_EXC_INFO || op == Pyc::RETURN_VALUE || op == Pyc::RETURN_CONST_A)
        return false;
    if (op == Pyc::JUMP_BACKWARD_A || op == Pyc::JUMP_BACKWARD_NO_INTERRUPT_A)
        return ast_relative_jump_target(mod, op, arg, next, true) != loopStart;
    if (op == Pyc::JUMP_ABSOLUTE_A)
        return arg * (int)sizeof(uint16_t) != loopStart;
    return true;
}

// Comparison of the chained middle operand extends the pending chain (`a < b` + `b < c` -> `a < b < c`)
static PycRef<ASTNode> ast_chain_compare(PycRef<ASTNode>& chainLeft, PycRef<ASTNode>& chainMiddle,
                                         PycRef<ASTNode> left, PycRef<ASTNode> right, int op)
{
    if (chainLeft != nullptr && left == chainMiddle) {
        PycRef<ASTCompare> chained = new ASTCompare(chainLeft, right, op);
        chained->setChained();
        chainLeft = nullptr;
        chainMiddle = nullptr;
        return chained.cast<ASTNode>();
    }
    return new ASTCompare(left, right, op);
}

// Instruction at `offset` for any version (wordcode from 3.6, variable length before)
static bool ast_read_any_instr(PycRef<PycCode> code, PycModule* mod, int offset, int& opcode, int& operand, int& next)
{
    if (mod->verCompare(3, 6) >= 0)
        return ast_read_wordcode_instr(code->code(), mod, offset, opcode, operand, next);
    PycBuffer buf(code->code()->value(), code->code()->length());
    if (offset < 0 || offset >= code->code()->length() || !buf.setPos(offset))
        return false;
    next = offset;
    bc_next(buf, mod, opcode, operand, next);
    return true;
}

// Cleanup of a chained comparison's short-circuit target (drops the copied middle): skip it when decoding linearly
static void ast_register_chain_cleanup(PycRef<PycCode> code, PycModule* mod, int from, int target,
                                       std::map<int, int>& chainSkipAt)
{
    int op = 0, arg = 0, next = 0, prev = -1, prevOp = 0, prevArg = 0, prevNext = 0;
    for (int at = from; at < target && ast_read_any_instr(code, mod, at, op, arg, next); at = next) {
        if (op == Pyc::CACHE)
            continue;
        prev = at;
        prevOp = op;
        prevArg = arg;
        prevNext = next;
    }
    if (prev < 0)
        return;
    // Value form: the final comparison jumps over the cleanup
    if (prevOp == Pyc::JUMP_FORWARD_A && ast_next_instr_offset_after_caches(mod, prevOp, prevNext) == target) {
        chainSkipAt[prev] = ast_relative_jump_target(mod, prevOp, prevArg, prevNext, false);
        return;
    }
    // Returning form: the cleanup repeats the return
    if (prevOp != Pyc::RETURN_VALUE && prevOp != Pyc::RETURN_CONST_A)
        return;
    int at = target;
    while (ast_read_any_instr(code, mod, at, op, arg, next)
            && (op == Pyc::CACHE || op == Pyc::ROT_TWO || op == Pyc::SWAP_A || op == Pyc::POP_TOP))
        at = next;
    if (op == Pyc::RETURN_VALUE)
        chainSkipAt[target] = next;
}

// Length of the short straight-line block at `start` that ends in a return (-1 otherwise)
static int ast_returning_block_len(PycRef<PycCode> code, PycModule* mod, int start)
{
    int op = 0, arg = 0, next = 0;
    for (int at = start; at < start + 48 && ast_read_wordcode_instr(code->code(), mod, at, op, arg, next); at = next) {
        if (op == Pyc::RETURN_VALUE || op == Pyc::RETURN_CONST_A)
            return next - start;
        if (op == Pyc::JUMP_FORWARD_A || op == Pyc::JUMP_BACKWARD_A || op == Pyc::PUSH_EXC_INFO
                || op == Pyc::POP_JUMP_IF_FALSE_A || op == Pyc::POP_JUMP_IF_TRUE_A
                || op == Pyc::POP_JUMP_IF_NONE_A || op == Pyc::POP_JUMP_IF_NOT_NONE_A
                || op == Pyc::FOR_ITER_A || op == Pyc::END_FOR || op == Pyc::RAISE_VARARGS_A)
            return -1;
    }
    return -1;
}

// Whether the last instruction before `blockEnd` is an unconditional jump to `target` (its offset in `at`)
static bool ast_closing_jump_to(PycRef<PycCode> code, PycModule* mod, int from, int blockEnd, int target, int& jumpAt)
{
    int op = 0, arg = 0, next = 0, last = -1, lastOp = -1, lastArg = 0, lastNext = 0;
    for (int at = from; at < blockEnd && ast_read_any_instr(code, mod, at, op, arg, next); at = next) {
        if (op == Pyc::CACHE || op == Pyc::NOT_TAKEN)
            continue;
        last = at;
        lastOp = op;
        lastArg = arg;
        lastNext = next;
    }
    int lastTarget = -1;
    if (lastOp == Pyc::JUMP_FORWARD_A)
        lastTarget = ast_relative_jump_target(mod, lastOp, lastArg, lastNext, false);
    else if (lastOp == Pyc::JUMP_ABSOLUTE_A)
        lastTarget = mod->verCompare(3, 10) >= 0 ? lastArg * 2 : lastArg;
    if (lastTarget < 0)
        return false;
    // The target may itself be an unconditional jump to the same destination (jump threading)
    int dest = target;
    if (lastTarget != target && ast_read_any_instr(code, mod, target, op, arg, next)) {
        if (op == Pyc::JUMP_ABSOLUTE_A)
            dest = mod->verCompare(3, 10) >= 0 ? arg * 2 : arg;
        else if (op == Pyc::JUMP_FORWARD_A)
            dest = ast_relative_jump_target(mod, op, arg, next, false);
        else if (op == Pyc::JUMP_BACKWARD_A)
            dest = ast_relative_jump_target(mod, op, arg, next, true);
    }
    if (lastTarget != dest)
        return false;
    jumpAt = last;
    return true;
}

// Whether the last instruction before `target` (scanning from `from`) leaves unconditionally
static bool ast_follows_unconditional_exit(PycRef<PycCode> code, PycModule* mod, int from, int target)
{
    int op = 0, arg = 0, next = 0, lastOp = -1;
    for (int at = from; at < target && ast_read_any_instr(code, mod, at, op, arg, next); at = next) {
        if (op != Pyc::CACHE && op != Pyc::NOT_TAKEN)
            lastOp = op;
    }
    return lastOp == Pyc::JUMP_FORWARD_A || lastOp == Pyc::JUMP_ABSOLUTE_A || lastOp == Pyc::JUMP_BACKWARD_A
        || lastOp == Pyc::RETURN_VALUE || lastOp == Pyc::RETURN_CONST_A || lastOp == Pyc::RAISE_VARARGS_A
        || lastOp == Pyc::BREAK_LOOP;
}

static void ast_consume_call_self_slot(FastStack& stack, PycRef<ASTNode>& func)
{
    if (func == nullptr && !stack.empty()) {
        func = stack.top();
        stack.pop();
    } else if (!stack.empty() && stack.top() == nullptr) {
        stack.pop();
    }
}

static bool ast_read_wordcode_instr(PycRef<PycString> bytes, PycModule* mod,
                                    int offset, int& opcode, int& operand, int& next)
{
    if (mod->verCompare(3, 6) < 0 || bytes == nullptr)
        return false;

    int length = bytes->length();
    if (offset < 0 || offset + 1 >= length)
        return false;

    const unsigned char* raw = (const unsigned char*)bytes->value();
    int ext = 0;

    while (offset + 1 < length) {
        opcode = Pyc::ByteToOpcode(mod->majorVer(), mod->minorVer(), raw[offset]);
        int oparg = raw[offset + 1];
        next = offset + 2;

        if (opcode != Pyc::EXTENDED_ARG_A) {
            operand = (ext << 8) | oparg;
            return true;
        }

        ext = (ext << 8) | oparg;
        offset = next;
    }

    return false;
}

static bool ast_is_synthetic_exception_cleanup(PycRef<PycCode> code, PycModule* mod,
                                               int offset, int& end)
{
    int opcode, operand, next;
    if (!ast_read_wordcode_instr(code->code(), mod, offset, opcode, operand, next))
        return false;
    // 3.15 loads None as common constant 7
    if (opcode == Pyc::LOAD_COMMON_CONSTANT_A) {
        if (operand != 7)
            return false;
    } else {
        if (opcode != Pyc::LOAD_CONST_A)
            return false;
        PycRef<PycObject> obj = code->getConst(operand);
        if (obj == nullptr || obj->type() != PycObject::TYPE_NONE)
            return false;
    }

    int store_op, store_arg, store_next;
    if (!ast_read_wordcode_instr(code->code(), mod, next, store_op, store_arg, store_next)
            || (store_op != Pyc::STORE_FAST_A && store_op != Pyc::STORE_DEREF_A))
        return false;

    int delete_op, delete_arg, delete_next;
    if (!ast_read_wordcode_instr(code->code(), mod, store_next, delete_op, delete_arg, delete_next)
            || delete_arg != store_arg)
        return false;

    if ((store_op == Pyc::STORE_FAST_A && delete_op != Pyc::DELETE_FAST_A)
            || (store_op == Pyc::STORE_DEREF_A && delete_op != Pyc::DELETE_DEREF_A))
        return false;

    end = delete_next;
    return true;
}

static PycRef<ASTCondBlock> ast_find_except_bind_block(PycRef<ASTBlock> curblock,
                                                       std::stack<PycRef<ASTBlock> > blocks)
{
    if (curblock != nullptr && curblock->blktype() == ASTBlock::BLK_EXCEPT) {
        PycRef<ASTCondBlock> except = curblock.try_cast<ASTCondBlock>();
        if (except != nullptr && except->cond() != nullptr)
            return except;
    }

    while (!blocks.empty()) {
        PycRef<ASTBlock> block = blocks.top();
        blocks.pop();
        if (block != nullptr && block->blktype() == ASTBlock::BLK_EXCEPT) {
            PycRef<ASTCondBlock> except = block.try_cast<ASTCondBlock>();
            if (except != nullptr && except->cond() != nullptr)
                return except;
        }
    }

    return nullptr;
}

/* compiler generates very, VERY similar byte code for if/else statement block and if-expression
 *  statement
 *      if a: b = 1
 *      else: b = 2
 *  expression:
 *      b = 1 if a else 2
 *  (see for instance https://stackoverflow.com/a/52202007)
 *  here, try to guess if just finished else statement is part of if-expression (ternary operator)
 *  if it is, remove statements from the block and put a ternary node on top of stack
 */
static void CheckIfExpr(FastStack& stack, PycRef<ASTBlock> curblock)
{
    if (stack.empty())
        return;
    if (curblock->nodes().size() < 2)
        return;
    auto rit = curblock->nodes().crbegin();
    // the last is "else" block, the one before should be "if" (could be "for", ...)
    if ((*rit)->type() != ASTNode::NODE_BLOCK ||
        (*rit).cast<ASTBlock>()->blktype() != ASTBlock::BLK_ELSE)
        return;
    PycRef<ASTBlock> else_block = (*rit).cast<ASTBlock>();
    ++rit;
    if ((*rit)->type() != ASTNode::NODE_BLOCK ||
        (*rit).cast<ASTBlock>()->blktype() != ASTBlock::BLK_IF)
        return;
    PycRef<ASTBlock> if_block_node = (*rit).cast<ASTBlock>();
    /* A conditional expression leaves its branch values on the value stack
       and therefore has empty statement blocks.  A surrounding for/with can
       also leave an unrelated value on the stack; do not consume that value
       and erase a real statement if/else. */
    if (if_block_node->size() != 0 || else_block->size() != 0)
        return;
    auto else_expr = StackPopTop(stack);
    curblock->removeLast();
    auto if_block = curblock->nodes().back();
    auto if_expr = StackPopTop(stack);
    curblock->removeLast();
    stack.push(new ASTTernary(std::move(if_block), std::move(if_expr), std::move(else_expr)));
}

PycRef<ASTNode> BuildFromCode(PycRef<PycCode> code, PycModule* mod);

/* Sentinel name representing the live exception pushed by PUSH_EXC_INFO
   (Python 3.11+). It is bound by `except ... as <var>` (a STORE) or discarded
   (a POP_TOP); it must never reach the output. */
static const char* const EXC_SENTINEL = "<exception value>";
static bool isExcSentinel(const PycRef<ASTNode>& node)
{
    return node != NULL && node.type() == ASTNode::NODE_NAME
            && node.cast<ASTName>()->name()->isEqual(EXC_SENTINEL);
}

static bool sameName(const PycRef<ASTNode>& a, const PycRef<ASTNode>& b)
{
    return a != NULL && b != NULL
            && a.type() == ASTNode::NODE_NAME && b.type() == ASTNode::NODE_NAME
            && a.cast<ASTName>()->name()->isEqual(b.cast<ASTName>()->name()->value());
}

/* Python 3.11 `except ... as <name>` binding plus its compiler cleanup. Returns
   true if the store was consumed (and should be suppressed). */
static bool handleExceptBinding(PycRef<ASTBlock>& curblock,
                                const PycRef<ASTNode>& value,
                                const PycRef<ASTNode>& name)
{
    if (curblock->blktype() != ASTBlock::BLK_EXCEPT)
        return false;
    PycRef<ASTCondBlock> exc = curblock.try_cast<ASTCondBlock>();
    if (exc == NULL)
        return false;
    if (isExcSentinel(value)) {            /* except <type> as <name>: */
        exc->setExceptVar(name);
        return true;
    }
    /* Compiler cleanup at the end of an `except ... as <name>` handler:
       `<name> = None; del <name>`. The store value may arrive either as a
       NULL placeholder or as an explicit None constant (LOAD_CONST None;
       STORE). Suppress both when the target is the bound exception var. */
    bool valueIsNone = (value == NULL)
            || (value != NULL && value.type() == ASTNode::NODE_OBJECT
                && value.cast<ASTObject>()->object() == Pyc_None);
    if (valueIsNone && exc->exceptVar() != NULL
            && sameName(name, exc->exceptVar()))
        return true;
    return false;
}

/* True if `del <name>` targets the bound exception variable (cleanup). */
static bool isExceptVarDelete(const PycRef<ASTBlock>& curblock,
                              const PycRef<ASTNode>& name)
{
    if (curblock->blktype() != ASTBlock::BLK_EXCEPT)
        return false;
    PycRef<ASTCondBlock> exc = curblock.try_cast<ASTCondBlock>();
    return exc != NULL && exc->exceptVar() != NULL
            && sameName(name, exc->exceptVar());
}

/* Search a decompiled comprehension/generator code body for the
   ASTComprehension node it produces (Python 3.x compiles comprehensions and
   generator expressions into separate code objects). */
static PycRef<ASTComprehension> FindComprehension(PycRef<ASTNode> node)
{
    if (node == NULL)
        return NULL;
    switch (node.type()) {
    case ASTNode::NODE_COMPREHENSION:
        return node.cast<ASTComprehension>();
    case ASTNode::NODE_RETURN:
        return FindComprehension(node.cast<ASTReturn>()->value());
    case ASTNode::NODE_STORE:
        return FindComprehension(node.cast<ASTStore>()->src());
    case ASTNode::NODE_NODELIST:
        for (const auto& n : node.cast<ASTNodeList>()->nodes()) {
            PycRef<ASTComprehension> c = FindComprehension(n);
            if (c != NULL)
                return c;
        }
        return NULL;
    default:
        return NULL;
    }
}

/* A generator expression compiles to a code object that yields rather than
   building a NODE_COMPREHENSION, so reconstruct it from its for-loop: the FOR
   block becomes the comprehension generator, the yielded value the result, and
   a wrapping `if` its filter. The caller substitutes the implicit ".0" iterator
   with the real iterable. */
/* Walk a comprehension for-loop body for the yielded value, descending through
   (possibly nested) `if` filters and combining their conditions with `and`.
   Returns the yielded value and, via outCond, the combined filter (or NULL). */
static PycRef<ASTNode> findCompYield(const ASTBlock::list_t& nodes,
                                     PycRef<ASTNode> condSoFar,
                                     PycRef<ASTNode>& outCond)
{
    PycRef<ASTNode> siblingFilter = condSoFar;
    for (const auto& n : nodes) {
        if (n.type() == ASTNode::NODE_RETURN
                && n.cast<ASTReturn>()->rettype() == ASTReturn::YIELD) {
            outCond = siblingFilter;
            return n.cast<ASTReturn>()->value();
        }
        if (n.type() == ASTNode::NODE_BLOCK
                && n.cast<ASTBlock>()->blktype() == ASTBlock::BLK_IF) {
            PycRef<ASTCondBlock> ifblk = n.cast<ASTCondBlock>();
            PycRef<ASTNode> c = ifblk->cond();
            if (ifblk->size() == 1
                    && ifblk->nodes().front().type() == ASTNode::NODE_KEYWORD
                    && ifblk->nodes().front().cast<ASTKeyword>()->key()
                        == ASTKeyword::KW_CONTINUE) {
                /* A generator filter commonly decompiles as
                   `if not condition: continue; yield value`. The filter for
                   the following sibling yield is the inverse of that branch. */
                if (!ifblk->negative())
                    c = new ASTUnary(c, ASTUnary::UN_NOT);
                siblingFilter = siblingFilter == NULL ? c
                        : new ASTBinary(siblingFilter, c,
                                ASTBinary::BIN_LOG_AND);
                continue;
            }
            if (ifblk->negative())
                c = new ASTUnary(c, ASTUnary::UN_NOT);
            PycRef<ASTNode> combined = (condSoFar == NULL) ? c
                    : new ASTBinary(condSoFar, c, ASTBinary::BIN_LOG_AND);
            PycRef<ASTNode> r = findCompYield(ifblk->nodes(), combined, outCond);
            if (r != NULL)
                return r;
        }
    }
    return NULL;
}

static PycRef<ASTComprehension> SynthGenexpr(PycRef<ASTNode> node)
{
    if (node == NULL)
        return NULL;
    if (node.type() == ASTNode::NODE_NODELIST) {
        for (const auto& n : node.cast<ASTNodeList>()->nodes()) {
            PycRef<ASTComprehension> c = SynthGenexpr(n);
            if (c != NULL)
                return c;
        }
        return NULL;
    }
    if (node.type() == ASTNode::NODE_BLOCK
            && node.cast<ASTBlock>()->blktype() == ASTBlock::BLK_FOR) {
        PycRef<ASTIterBlock> forblk = node.cast<ASTIterBlock>();
        PycRef<ASTNode> cond;
        PycRef<ASTNode> result = findCompYield(forblk->nodes(), NULL, cond);
        if (result == NULL)
            return NULL;
        if (cond != NULL)
            forblk->setCondition(cond);
        PycRef<ASTComprehension> comp = new ASTComprehension(result, true);
        comp->addGenerator(forblk);
        return comp;
    }
    return NULL;
}

static bool ast_is_comp_code(PycRef<PycCode> code)
{
    if (code == nullptr || code->name() == nullptr)
        return false;
    const char* cn = code->name()->value();
    return cn && (!strcmp(cn, "<listcomp>") || !strcmp(cn, "<setcomp>")
            || !strcmp(cn, "<dictcomp>") || !strcmp(cn, "<genexpr>"));
}

// Next non-cache instruction is `want`. NOT_TAKEN is a 3.13+ hint, not an operation.
static bool ast_next_real_is(PycRef<PycCode> code, PycModule* mod, int at, int want)
{
    int op = 0, arg = 0, next = 0;
    while (code != nullptr && code->code() != nullptr
            && ast_read_wordcode_instr(code->code(), mod, at, op, arg, next)) {
        if (op == Pyc::CACHE || op == Pyc::NOP || op == Pyc::NOT_TAKEN
                || op == Pyc::INSTRUMENTED_NOT_TAKEN_A)
            at = next;
        else
            return op == want;
    }
    return false;
}

// Offset of the async-for terminator, or the end of the code object if it is absent.
static int ast_async_for_end(PycRef<PycCode> code, PycModule* mod, int at)
{
    int end = code != nullptr && code->code() != nullptr ? code->code()->length() : at;
    int op = 0, arg = 0, next = 0;
    while (code != nullptr && code->code() != nullptr
            && ast_read_wordcode_instr(code->code(), mod, at, op, arg, next)) {
        if (op == Pyc::END_ASYNC_FOR || op == Pyc::END_ASYNC_FOR_A
                || op == Pyc::INSTRUMENTED_END_ASYNC_FOR_A)
            return at;
        at = next;
    }
    return end;
}

// A comprehension code object called with its iterable: rebuild the comprehension with .0 replaced by that iterable
static PycRef<ASTNode> ast_inline_comprehension(PycRef<ASTNode> func, PycRef<ASTNode> iter, PycModule* mod)
{
    if (func.type() != ASTNode::NODE_FUNCTION)
        return nullptr;
    PycRef<ASTObject> codeObj = func.cast<ASTFunction>()->code().try_cast<ASTObject>();
    PycRef<PycCode> ccode;
    if (codeObj != nullptr)
        ccode = codeObj->object().try_cast<PycCode>();
    if (ccode == nullptr || ccode->name() == nullptr)
        return nullptr;
    const char* nm = ccode->name()->value();
    if (strcmp(nm, "<listcomp>") && strcmp(nm, "<setcomp>")
            && strcmp(nm, "<dictcomp>") && strcmp(nm, "<genexpr>"))
        return nullptr;
    bool savedClean = cleanBuild;
    PycRef<ASTNode> compAst = BuildFromCode(ccode, mod);
    cleanBuild = savedClean;
    PycRef<ASTComprehension> comp = FindComprehension(compAst);
    if (comp == nullptr) {
        comp = SynthGenexpr(compAst);
        // A filtered <listcomp> body is rebuilt through the yield path; keep it a list comprehension
        if (comp != nullptr && !strcmp(nm, "<listcomp>")) {
            PycRef<ASTComprehension> listComp = new ASTComprehension(comp->result());
            ASTComprehension::generator_t gens = comp->generators();
            for (auto gen = gens.rbegin(); gen != gens.rend(); ++gen)
                listComp->addGenerator(*gen);
            comp = listComp;
        }
    }
    if (comp == nullptr || comp->generators().empty())
        return nullptr;
    comp->generators().front()->setIter(iter);
    return comp.cast<ASTNode>();
}

/* Python 3.11 with-statement pre-pass. For each BEFORE_WITH whose normal exit
   has the canonical shape (body -> implicit __exit__ -> JUMP over the cleanup
   handler -> resume), record the with body end and the resume offset. The
   region [bodyEnd, resume) (implicit __exit__ call + jump + exception cleanup
   handler) is then skipped during decompilation. With-statements without this
   clean shape are left unhandled (no regression). */
static void ScanWithBlocks(PycRef<PycCode> code, PycModule* mod,
                           const std::vector<PycExceptionTableEntry>& entries,
                           std::map<int, int>& bodyEndByBefore,
                           std::map<int, int>& resumeByBodyEnd,
                           std::map<int, int>& returnCleanupUntil,
                           std::map<int, int>& handlerEndByStart)
{
    PycBuffer src(code->code()->value(), code->code()->length());
    int opcode, operand, pos = 0;
    std::vector<int> befores;
    std::vector<std::pair<int, int>> fwdJumps;   /* (pos, target) */
    std::map<int, int> opcodeAt;                 /* pos -> opcode */
    std::map<int, int> operandAt;                /* pos -> operand */
    std::map<int, int> nextAt;                   /* pos -> next instruction */
    while (!src.atEof()) {
        int p = pos;
        bc_next(src, mod, opcode, operand, pos);
        opcodeAt[p] = opcode;
        operandAt[p] = operand;
        nextAt[p] = pos;
        if (opcode == Pyc::BEFORE_WITH
                || (opcode == Pyc::LOAD_SPECIAL_A && operand == 0))
            befores.push_back(p);
        else if (opcode == Pyc::JUMP_FORWARD_A)
            fwdJumps.push_back(std::make_pair(p, pos + operand * 2));
    }
    auto nextRealInstruction = [&opcodeAt, &nextAt](int at) {
        std::map<int, int>::const_iterator next = nextAt.find(at);
        if (next == nextAt.end())
            return -1;
        int p = next->second;
        while (p >= 0) {
            std::map<int, int>::const_iterator op = opcodeAt.find(p);
            if (op == opcodeAt.end() || op->second != Pyc::CACHE)
                break;
            next = nextAt.find(p);
            if (next == nextAt.end())
                return -1;
            p = next->second;
        }
        return p;
    };
    auto isCleanupNone = [&opcodeAt, &operandAt](int p) {
        if (p < 0)
            return false;
        if (opcodeAt[p] == Pyc::LOAD_CONST_A)
            return true;
        // 3.15 loads the three None arguments of the implicit __exit__ from the common-constant pool
        return opcodeAt[p] == Pyc::LOAD_COMMON_CONSTANT_A && operandAt[p] == 7;
    };
    auto hasNormalCleanupAfter = [&opcodeAt, &nextRealInstruction, &isCleanupNone](int bodyEnd) {
        int p = bodyEnd;
        while (p >= 0 && opcodeAt[p] == Pyc::CACHE)
            p = nextRealInstruction(p);
        while (p >= 0 && (opcodeAt[p] == Pyc::END_FOR
                || opcodeAt[p] == Pyc::INSTRUMENTED_END_FOR_A
                || opcodeAt[p] == Pyc::POP_TOP))
            p = nextRealInstruction(p);
        for (int i = 0; i < 3; i++) {
            if (!isCleanupNone(p))
                return false;
            p = nextRealInstruction(p);
        }
        if (p < 0 || opcodeAt[p] != Pyc::CALL_A)
            return false;
        p = nextRealInstruction(p);
        return p >= 0 && opcodeAt[p] == Pyc::POP_TOP;
    };
    for (int bp : befores) {
        int bodyEnd = -1, handler = -1;
        for (const auto& e : entries) {
            if (e.start_offset <= bp)
                continue;
            auto h0 = opcodeAt.find(e.target);
            if (h0 == opcodeAt.end() || h0->second != Pyc::PUSH_EXC_INFO)
                continue;
            auto h1 = opcodeAt.find(nextAt[e.target]);
            if (h1 == opcodeAt.end() || h1->second != Pyc::WITH_EXCEPT_START)
                continue;
            handler = e.target;
            break;
        }
        if (handler < 0)
            continue;

        /* Python 3.13 splits a with body around branches, but every protected
           range uses the same WITH_EXCEPT_START handler. The normal cleanup
           begins after the last such range, not after the first one. */
        for (const auto& e : entries) {
            if (e.target == handler && e.push_lasti && e.start_offset > bp
                    && e.end_offset > bodyEnd)
                bodyEnd = e.end_offset;
        }
        /* A handler can protect its own re-raise cleanup with an entry ending
           at the handler address.  That entry is not part of the with body;
           in this one shape select the last protected range followed by the
           canonical normal __exit__ call instead. */
        if (bodyEnd == handler) {
            bodyEnd = -1;
            for (const auto& e : entries) {
                if (e.target == handler && e.push_lasti && e.start_offset > bp
                        && e.end_offset < handler && e.end_offset > bodyEnd
                        && hasNormalCleanupAfter(e.end_offset))
                    bodyEnd = e.end_offset;
            }
        }
        if (bodyEnd < 0)
            continue;
        if (opcodeAt[bodyEnd] == Pyc::JUMP_BACKWARD_A
                || opcodeAt[bodyEnd] == Pyc::JUMP_BACKWARD_NO_INTERRUPT_A
                || opcodeAt[bodyEnd] == Pyc::INSTRUMENTED_JUMP_BACKWARD_A) {
            /* The exception-table end can name a loop's final back-edge. Keep
               that instruction in the with body so it can close the loop; the
               implicit __exit__ call starts at the next real instruction. */
            bodyEnd = nextRealInstruction(bodyEnd);
        }

        int resume = -1;
        for (const auto& jp : fwdJumps) {
            /* The normal-exit jump sits between the body end and the handler and
               jumps over the handler (target at/after it). */
            if (jp.first >= bodyEnd && jp.first < handler && jp.second >= handler) {
                resume = jp.second;
                break;
            }
        }
        int cleanupStart = bodyEnd;
        while (cleanupStart >= 0 && opcodeAt[cleanupStart] == Pyc::CACHE)
            cleanupStart = nextRealInstruction(cleanupStart);
        if (resume < 0 && cleanupStart >= 0 && isCleanupNone(cleanupStart)) {
            /* A terminal 3.13 with body has no jump over the handler: the
               implicit __exit__(None, None, None) call is followed directly
               by return/control-flow outside the with statement. */
            for (const auto& kv : nextAt) {
                int cleanup = kv.first;
                if (cleanup <= bodyEnd || cleanup >= handler)
                    continue;
                if (opcodeAt[cleanup] == Pyc::POP_TOP) {
                    resume = kv.second;
                    break;
                }
            }
        }
        if (resume < 0)
            continue;   /* only the clean jump-over-handler shape */
        bodyEndByBefore[bp] = bodyEnd;
        resumeByBodyEnd[bodyEnd] = resume;

        if (mod->verCompare(3, 14) >= 0 && !handlerEndByStart.count(handler)) {
            for (auto it = opcodeAt.lower_bound(handler); it != opcodeAt.end(); ++it) {
                if (it->second != Pyc::COPY_A || operandAt[it->first] != 3)
                    continue;
                int pop = nextRealInstruction(it->first);
                int rer = pop >= 0 ? nextRealInstruction(pop) : -1;
                if (pop >= 0 && rer >= 0 && opcodeAt[pop] == Pyc::POP_EXCEPT
                        && (opcodeAt[rer] == Pyc::RERAISE
                                || opcodeAt[rer] == Pyc::RERAISE_A)
                        && operandAt[rer] == 1) {
                    handlerEndByStart[handler] = nextAt[rer];
                    break;
                }
            }
        }

        /* A return from inside a Python 3.13 with body first shuffles the
           return value around the hidden __exit__ callable, then invokes the
           callable with three None arguments.  That housekeeping is not a
           source expression; if interpreted normally it becomes spurious
           `manager` / `value(None, None)` nodes and loses the return value.
           Recognize only the exact compiler sequence and leave the following
           RETURN_VALUE to consume the original value. */
        for (const auto& kv : opcodeAt) {
            int cleanup = kv.first;
            if (cleanup < bp || cleanup >= bodyEnd || kv.second != Pyc::SWAP_A)
                continue;
            int p = nextRealInstruction(cleanup);
            if (p < 0 || opcodeAt[p] != Pyc::POP_TOP)
                continue;
            p = nextRealInstruction(p);
            if (p < 0 || opcodeAt[p] != Pyc::SWAP_A)
                continue;
            p = nextRealInstruction(p);
            bool noneArgs = true;
            for (int i = 0; i < 3; i++) {
                if (!isCleanupNone(p)) {
                    noneArgs = false;
                    break;
                }
                p = nextRealInstruction(p);
            }
            if (!noneArgs || p < 0 || opcodeAt[p] != Pyc::CALL_A)
                continue;
            p = nextRealInstruction(p);
            if (p < 0 || opcodeAt[p] != Pyc::POP_TOP)
                continue;
            int ret = nextRealInstruction(p);
            if (ret < 0)
                continue;
            if (opcodeAt[ret] == Pyc::RETURN_VALUE
                    || opcodeAt[ret] == Pyc::INSTRUMENTED_RETURN_VALUE_A) {
                returnCleanupUntil[cleanup] = ret;
            }
        }
    }
}

/* Python 3.11+ exception tables describe only protected instruction ranges;
   a normal try body can therefore end long before its handler appears in the
   linear stream.  Record short ranges that do not hand directly into a with
   setup.  With setup is handled by ScanWithBlocks because its implicit cleanup
   extends the source-level body beyond the protected setup range. */
/* Python 3.11 try/finally pre-pass. A finally compiles to: try body -> finally
   body (normal copy) -> JUMP over an exception handler that duplicates the
   finally body and re-raises. Recognize it from the exception table and record,
   per try-body entry start: the try body end, the finally block end (the JUMP
   over the duplicate), and the resume offset. The duplicate handler region is
   skipped during decompilation. Distinguishes finally from except handlers:
   after PUSH_EXC_INFO a finally has neither a POP_TOP (bare except) nor a
   CHECK_EXC_MATCH (typed except). */
// 3.11+ try/finally with the finally body taken from its handler: skip every inline copy so the try runs up to the handler
static bool ast_scan_finally_handler(PycRef<PycCode> code, PycModule* mod,
                                     const std::vector<PycExceptionTableEntry>& entries, int T,
                                     std::map<int, int>& tryEndByStart, std::map<int, int>& finallyEndByStart,
                                     std::map<int, int>& resumeByFinallyEnd, std::set<int>& skip,
                                     std::map<int, int>& handlerByStart)
{
    PycBuffer src(code->code()->value(), code->code()->length());
    std::vector<int> at, op, arg, next;
    int opcode, operand, pos = 0;
    while (!src.atEof()) {
        int p = pos;
        bc_next(src, mod, opcode, operand, pos);
        at.push_back(p); op.push_back(opcode); arg.push_back(operand); next.push_back(pos);
    }
    std::map<int, int> indexAt;
    for (size_t i = 0; i < at.size(); i++)
        indexAt[at[i]] = (int)i;
    auto ti = indexAt.find(T);
    if (ti == indexAt.end() || op[ti->second] != Pyc::PUSH_EXC_INFO)
        return false;
    const int h = ti->second + 1;
    // Finally body ends at the handler's RERAISE; a nested handler inside it is left to the old logic
    int r = h;
    while (r < (int)op.size() && op[r] != Pyc::RERAISE_A && op[r] != Pyc::RERAISE
            && op[r] != Pyc::CHECK_EXC_MATCH && op[r] != Pyc::PUSH_EXC_INFO)
        r++;
    if (r >= (int)op.size() || r == h || (op[r] != Pyc::RERAISE_A && op[r] != Pyc::RERAISE)
            || op[h] == Pyc::POP_TOP)
        return false;
    // A non-lasti entry inside the handler is a nested try, unless it is only the await SEND edge
    for (const auto& e : entries) {
        if (e.push_lasti || e.start_offset <= T || e.start_offset >= at[r])
            continue;
        auto tgt = indexAt.find(e.target);
        if (tgt != indexAt.end() && (op[tgt->second] == Pyc::CLEANUP_THROW
                || op[tgt->second] == Pyc::END_ASYNC_FOR || op[tgt->second] == Pyc::END_ASYNC_FOR_A
                || op[tgt->second] == Pyc::INSTRUMENTED_END_ASYNC_FOR_A))
            continue;
        return false;
    }
    // Cleanup handler of the finally handler: COPY 3; POP_EXCEPT; RERAISE 1
    int cleanupEnd = -1;
    for (const auto& e : entries) {
        if (e.push_lasti && e.start_offset == T) {
            auto ci = indexAt.find(e.target);
            if (ci != indexAt.end() && ci->second + 2 < (int)op.size()
                    && op[ci->second] == Pyc::COPY_A && op[ci->second + 1] == Pyc::POP_EXCEPT
                    && (op[ci->second + 2] == Pyc::RERAISE_A || op[ci->second + 2] == Pyc::RERAISE))
                cleanupEnd = next[ci->second + 2];
        }
    }
    if (cleanupEnd < 0)
        return false;
    int start = -1;
    for (const auto& e : entries) {
        if (!e.push_lasti && e.target == T && (start < 0 || e.start_offset < start))
            start = e.start_offset;
    }
    // Inner try/except regions whose handlers lie inside the protected range belong to the same try
    for (bool grew = start >= 0; grew; ) {
        grew = false;
        for (const auto& e : entries) {
            if (e.target >= start && e.target < T && e.start_offset < start) {
                start = e.start_offset;
                grew = true;
            }
        }
    }
    auto si = indexAt.find(start);
    if (start < 0 || si == indexAt.end())
        return false;

    auto norm = [](int o) {
        if (o == Pyc::LOAD_FAST_BORROW_A || o == Pyc::LOAD_FAST_CHECK_A)
            return (int)Pyc::LOAD_FAST_A;
        if (o == Pyc::LOAD_FAST_BORROW_LOAD_FAST_BORROW_A)
            return (int)Pyc::LOAD_FAST_LOAD_FAST_A;
        return o;
    };
    auto isJump = [](int o) {
        return o == Pyc::JUMP_FORWARD_A || o == Pyc::JUMP_BACKWARD_A || o == Pyc::JUMP_BACKWARD_NO_INTERRUPT_A
            || o == Pyc::POP_JUMP_IF_FALSE_A || o == Pyc::POP_JUMP_IF_TRUE_A
            || o == Pyc::POP_JUMP_IF_NONE_A || o == Pyc::POP_JUMP_IF_NOT_NONE_A
            || o == Pyc::POP_JUMP_FORWARD_IF_FALSE_A || o == Pyc::POP_JUMP_FORWARD_IF_TRUE_A
            || o == Pyc::POP_JUMP_FORWARD_IF_NONE_A || o == Pyc::POP_JUMP_FORWARD_IF_NOT_NONE_A
            || o == Pyc::SEND_A || o == Pyc::YIELD_VALUE || o == Pyc::YIELD_VALUE_A
            || o == Pyc::RESUME_A || o == Pyc::INSTRUMENTED_RESUME_A;
    };
    // SEND's exception edge sits inside the handler copy but after the inline copy
    auto skipNoise = [&](int& i, int limit) {
        while (i < limit && (op[i] == Pyc::CACHE || op[i] == Pyc::CLEANUP_THROW)) {
            if (op[i] == Pyc::CLEANUP_THROW) {
                i++;
                if (i < limit && (op[i] == Pyc::JUMP_BACKWARD_A || op[i] == Pyc::JUMP_BACKWARD_NO_INTERRUPT_A
                        || op[i] == Pyc::JUMP_FORWARD_A))
                    i++;
            } else {
                i++;
            }
        }
    };
    auto sameBody = [&](int k, int& endOut) {
        int a = k, b = h;
        while (true) {
            skipNoise(a, ti->second);
            skipNoise(b, r);
            if (b >= r) {
                endOut = a;
                return a > k;
            }
            if (a >= ti->second || norm(op[a]) != norm(op[b]))
                return false;
            if (!isJump(op[a]) && arg[a] != arg[b])
                return false;
            a++;
            b++;
        }
    };
    std::vector<int> copies;
    std::vector<int> copyEnds;
    for (int k = si->second; k < ti->second; k++) {
        int endK = k;
        if (sameBody(k, endK)) {
            copies.push_back(k);
            copyEnds.push_back(endK);
            k = endK - 1;
        }
    }
    if (copies.empty())
        return false;
    for (size_t ci = 0; ci < copies.size(); ci++) {
        int k = copies[ci];
        for (int j = k; j < copyEnds[ci]; j++)
            skip.insert(at[j]);
        // A jump that only resumes after the try statement belongs to the skipped copy
        int after = copyEnds[ci];
        while (after < (int)op.size() && op[after] == Pyc::CACHE)
            after++;
        if (after < (int)op.size() && (op[after] == Pyc::JUMP_FORWARD_A || op[after] == Pyc::JUMP_BACKWARD_A)
                && ast_relative_jump_target(mod, op[after], arg[after], next[after],
                                            op[after] != Pyc::JUMP_FORWARD_A) == cleanupEnd)
            skip.insert(at[after]);
    }
    skip.insert(-T);
    tryEndByStart[start] = T;
    handlerByStart[start] = T;
    finallyEndByStart[start] = at[r];
    resumeByFinallyEnd[at[r]] = cleanupEnd;
    return true;
}

static void ScanTryFinally(PycRef<PycCode> code, PycModule* mod,
                            const std::vector<PycExceptionTableEntry>& entries,
                            std::map<int, int>& tryEndByStart,
                            std::map<int, int>& finallyEndByStart,
                            std::map<int, int>& resumeByFinallyEnd,
                            std::map<int, int>& returnByStart,
                            std::set<int>& copySkip,
                            std::map<int, int>& handlerByStart)
{
    PycBuffer src(code->code()->value(), code->code()->length());
    int opcode, operand, pos = 0;
    std::map<int, int> opcodeAt;
    std::map<int, int> nextAt;
    std::vector<std::pair<int, int>> fwdJumps;
    while (!src.atEof()) {
        int p = pos;
        bc_next(src, mod, opcode, operand, pos);
        opcodeAt[p] = opcode;
        nextAt[p] = pos;
        if (opcode == Pyc::JUMP_FORWARD_A)
            fwdJumps.push_back(std::make_pair(p, pos + operand * 2));
    }
    std::set<int> handled;
    for (const auto& e : entries) {
        if (e.push_lasti)
            continue;                       /* try-body entries are lasti=False */
        int T = e.target;
        if (handled.count(T))
            continue;
        if (ast_scan_finally_handler(code, mod, entries, T, tryEndByStart, finallyEndByStart,
                                     resumeByFinallyEnd, copySkip, handlerByStart)) {
            handled.insert(T);
            continue;
        }
        auto h0 = opcodeAt.find(T);
        if (h0 == opcodeAt.end() || h0->second != Pyc::PUSH_EXC_INFO)
            continue;
        /* handler region end: the exception entry that starts at the handler */
        int handlerEnd = -1;
        for (const auto& e2 : entries) {
            if (e2.start_offset == T) { handlerEnd = e2.end_offset; break; }
        }
        if (handlerEnd < 0)
            continue;
        auto h1 = opcodeAt.find(T + 2);
        if (h1 != opcodeAt.end() && h1->second == Pyc::POP_TOP)
            continue;                       /* bare except, not finally */
        bool hasCheck = false;
        for (const auto& kv : opcodeAt) {
            if (kv.first >= T && kv.first < handlerEnd
                    && kv.second == Pyc::CHECK_EXC_MATCH) {
                hasCheck = true;
                break;
            }
        }
        if (hasCheck)
            continue;                       /* typed except, not finally */
        /* The normal finally copy ends with a JUMP over the handler. */
        int jumpPos = -1, resume = -1;
        for (const auto& jp : fwdJumps) {
            if (jp.first >= e.end_offset && jp.first < T && jp.second >= T) {
                jumpPos = jp.first;
                resume = jp.second;
                break;
            }
        }
        if (jumpPos >= 0) {
            handlerByStart[e.start_offset] = T;
            tryEndByStart[e.start_offset] = e.end_offset;
            finallyEndByStart[e.start_offset] = jumpPos;
            resumeByFinallyEnd[jumpPos] = resume;
            continue;
        }

        /* A terminal return in a try/finally has no jump over the handler:
           CPython leaves the computed return value on the stack, runs the
           normal finally copy, then immediately returns.  The duplicated
           exception copy is unreachable on this linear path. */
        int returnPos = -1;
        for (const auto& kv : opcodeAt) {
            if (kv.first < e.end_offset || kv.first >= T)
                continue;
            if ((kv.second == Pyc::RETURN_VALUE
                        || kv.second == Pyc::INSTRUMENTED_RETURN_VALUE_A)
                    && nextAt[kv.first] == T) {
                returnPos = kv.first;
                break;
            }
        }
        if (returnPos < 0)
            continue;

        int cleanupEnd = -1;
        for (const auto& kv : opcodeAt) {
            if (kv.first >= handlerEnd
                    && (kv.second == Pyc::RERAISE || kv.second == Pyc::RERAISE_A))
                cleanupEnd = nextAt[kv.first];
        }
        if (cleanupEnd <= handlerEnd)
            continue;

        handlerByStart[e.start_offset] = T;
        tryEndByStart[e.start_offset] = e.end_offset;
        finallyEndByStart[e.start_offset] = returnPos;
        resumeByFinallyEnd[returnPos] = cleanupEnd;
        returnByStart[e.start_offset] = returnPos;
    }
}

/* Python 3.13 inlines comprehensions into the enclosing code object.  The
   compiler protects the result container and saved fast-local slots with an
   exception-table entry whose handler only restores those locals and reraises.
   Record that synthetic region so it is not rendered as source try/except. */
static void ScanInlineComprehensions(PycRef<PycCode> code, PycModule* mod,
        const std::vector<PycExceptionTableEntry>& entries,
        std::map<int, int>& savedByStart,
        std::set<int>& syntheticTargets,
        std::map<int, int>& skipByTarget,
        std::set<int>& restoreStores)
{
    if (mod->verCompare(3, 12) < 0)
        return;

    PycBuffer src(code->code()->value(), code->code()->length());
    int opcode, operand, pos = 0;
    std::map<int, int> opcodeAt, operandAt, nextAt, prevAt;
    int previous = -1;
    while (!src.atEof()) {
        int p = pos;
        bc_next(src, mod, opcode, operand, pos);
        opcodeAt[p] = opcode;
        operandAt[p] = operand;
        nextAt[p] = pos;
        prevAt[p] = previous;
        previous = p;
    }

    auto previousRealInstruction = [&opcodeAt, &prevAt](int at) {
        auto prev = prevAt.find(at);
        if (prev == prevAt.end())
            return -1;
        int p = prev->second;
        while (p >= 0 && opcodeAt[p] == Pyc::CACHE) {
            prev = prevAt.find(p);
            if (prev == prevAt.end())
                return -1;
            p = prev->second;
        }
        return p;
    };
    auto nextRealInstruction = [&opcodeAt, &nextAt](int at) {
        auto next = nextAt.find(at);
        if (next == nextAt.end())
            return -1;
        int p = next->second;
        while (p >= 0 && opcodeAt[p] == Pyc::CACHE) {
            next = nextAt.find(p);
            if (next == nextAt.end())
                return -1;
            p = next->second;
        }
        return p;
    };

    for (const auto& entry : entries) {
        if (entry.push_lasti || entry.stack_depth < 2)
            continue;
        auto start = opcodeAt.find(entry.start_offset);
        if (start == opcodeAt.end()
                || (start->second != Pyc::BUILD_LIST_A
                    && start->second != Pyc::BUILD_MAP_A
                    && start->second != Pyc::BUILD_SET_A))
            continue;

        int setupSwap = previousRealInstruction(entry.start_offset);
        if (setupSwap < 0 || opcodeAt[setupSwap] != Pyc::SWAP_A
                || operandAt[setupSwap] < 2)
            continue;
        int saved = operandAt[setupSwap] - 1;
        int cleared = 0;
        std::multiset<int> savedLocals;
        for (int p = previousRealInstruction(setupSwap);
                p >= 0 && opcodeAt[p] == Pyc::LOAD_FAST_AND_CLEAR_A;
                p = previousRealInstruction(p)) {
            cleared++;
            savedLocals.insert(operandAt[p]);
        }
        if (cleared != saved)
            continue;
        int protectedEnd = entry.end_offset;
        for (const auto& other : entries) {
            if (!other.push_lasti && other.target == entry.target
                    && other.stack_depth == entry.stack_depth)
                protectedEnd = std::max(protectedEnd, other.end_offset);
        }

        int p = entry.target;
        auto op = opcodeAt.find(p);
        if (op == opcodeAt.end() || op->second != Pyc::SWAP_A)
            continue;
        p = nextAt[p];
        if (opcodeAt[p] != Pyc::POP_TOP)
            continue;
        p = nextAt[p];
        if (opcodeAt[p] != Pyc::SWAP_A)
            continue;

        int cleanupEnd = -1;
        for (const auto& kv : opcodeAt) {
            if (kv.first >= entry.target
                    && (kv.second == Pyc::RERAISE || kv.second == Pyc::RERAISE_A)) {
                cleanupEnd = nextAt[kv.first];
                break;
            }
        }
        if (cleanupEnd < 0)
            continue;

        // Restores of the saved locals follow the loop; static swap elimination may put the consumer's store first
        std::vector<int> restorePositions;
        p = protectedEnd;
        for (int scanned = 0; p >= 0 && scanned < saved + 8 && !savedLocals.empty(); scanned++) {
            if (opcodeAt[p] == Pyc::STORE_FAST_A && savedLocals.count(operandAt[p])) {
                savedLocals.erase(savedLocals.find(operandAt[p]));
                restorePositions.push_back(p);
            }
            p = nextRealInstruction(p);
        }
        if (static_cast<int>(restorePositions.size()) != saved)
            continue;
        restoreStores.insert(restorePositions.begin(), restorePositions.end());

        savedByStart[entry.start_offset] = saved;
        syntheticTargets.insert(entry.target);
        skipByTarget[entry.target] = cleanupEnd;
    }
}

/* Python 3.11 while-loop pre-pass. A while loop with the standard bottom-test
   layout compiles to:
        <eval cond>; POP_JUMP_FORWARD_IF_FALSE end     (entry guard)
   loop_start:
        <body>
        <eval cond>; POP_JUMP_BACKWARD_IF_TRUE loop_start   (back-edge)
   end:
   Without recognition pycdc renders both halves as independent `if` blocks and
   never forms the loop (the body's trailing back-edge becomes `if not cond:
   pass`). Detect it from a conditional backward jump whose target is the
   instruction immediately following a matching forward guard, and whose guard
   skips to the instruction right after the back-edge. Record the guard position
   (the BLK_WHILE opens there) and the back-edge position (the loop closes
   there). */
// 3.0-3.10 `except E as name`: find the compiler's `name = None; del name` try/finally and mark its instructions to skip
static void ScanExceptAsCleanup(PycRef<PycCode> code, PycModule* mod,
                                std::set<int>& skip, std::set<int>& bindStores)
{
    if (mod->verCompare(3, 0) < 0 || mod->verCompare(3, 11) >= 0)
        return;
    PycBuffer src(code->code()->value(), code->code()->length());
    std::vector<int> at, op, arg, next;
    int opcode, operand, pos = 0;
    while (!src.atEof()) {
        int p = pos;
        bc_next(src, mod, opcode, operand, pos);
        at.push_back(p); op.push_back(opcode); arg.push_back(operand); next.push_back(pos);
    }
    std::map<int, int> indexAt;
    for (size_t i = 0; i < at.size(); i++)
        indexAt[at[i]] = (int)i;
    auto isStore = [](int o) {
        return o == Pyc::STORE_FAST_A || o == Pyc::STORE_NAME_A
            || o == Pyc::STORE_DEREF_A || o == Pyc::STORE_GLOBAL_A;
    };
    auto deleteFor = [](int o) {
        return o == Pyc::STORE_FAST_A ? Pyc::DELETE_FAST_A
             : o == Pyc::STORE_NAME_A ? Pyc::DELETE_NAME_A
             : o == Pyc::STORE_DEREF_A ? Pyc::DELETE_DEREF_A : Pyc::DELETE_GLOBAL_A;
    };
    auto isNone = [&](size_t i) {
        if (op[i] != Pyc::LOAD_CONST_A)
            return false;
        PycRef<PycObject> c = code->getConst(arg[i]);
        return c != nullptr && c->type() == PycObject::TYPE_NONE;
    };
    // LOAD_CONST None; STORE name; DELETE name
    auto isClear = [&](size_t i, int storeOp, int storeArg) {
        return i + 2 < op.size() && isNone(i) && op[i + 1] == storeOp && arg[i + 1] == storeArg
            && op[i + 2] == deleteFor(storeOp) && arg[i + 2] == storeArg;
    };
    for (size_t i = 1; i + 3 < op.size(); i++) {
        if (op[i] != Pyc::POP_TOP || !isStore(op[i + 1]) || op[i + 2] != Pyc::POP_TOP
                || op[i + 3] != Pyc::SETUP_FINALLY_A)
            continue;
        if (op[i - 1] != Pyc::POP_JUMP_IF_FALSE_A && op[i - 1] != Pyc::JUMP_IF_NOT_EXC_MATCH_A)
            continue;
        const int storeOp = op[i + 1], storeArg = arg[i + 1];
        int cleanup = next[i + 3] + arg[i + 3] * (mod->verCompare(3, 10) >= 0 ? 2 : 1);
        auto ci = indexAt.find(cleanup);
        if (ci == indexAt.end() || !isClear(ci->second, storeOp, storeArg))
            continue;
        size_t tail = ci->second + 3;
        int tailOp = mod->verCompare(3, 9) >= 0 ? Pyc::RERAISE : Pyc::END_FINALLY;
        if (tail >= op.size() || (op[tail] != tailOp && op[tail] != Pyc::RERAISE_A))
            continue;

        bindStores.insert(at[i + 1]);
        skip.insert(at[i + 3]);
        for (size_t k = ci->second; k <= tail; k++)
            skip.insert(at[k]);
        int depth = 0;
        for (size_t k = i + 4; k < (size_t)ci->second; k++) {
            int o = op[k];
            if (o == Pyc::SETUP_FINALLY_A || o == Pyc::SETUP_EXCEPT_A || o == Pyc::SETUP_LOOP_A
                    || o == Pyc::SETUP_WITH_A || o == Pyc::SETUP_ASYNC_WITH_A) {
                depth++;
            } else if (o == Pyc::POP_BLOCK) {
                if (depth == 0) {
                    skip.insert(at[k]);
                    // <= 3.7 normal exit: POP_BLOCK; LOAD_CONST None (pushes the finally "no exception" marker)
                    if (mod->verCompare(3, 8) < 0 && k + 1 == (size_t)ci->second - 1 && isNone(k + 1))
                        skip.insert(at[k + 1]);
                } else {
                    depth--;
                }
            } else if (o == Pyc::CALL_FINALLY_A && next[k] + arg[k] == cleanup) {
                skip.insert(at[k]);
            } else if (o == Pyc::BEGIN_FINALLY && k + 1 == (size_t)ci->second) {
                skip.insert(at[k]);
            } else if (mod->verCompare(3, 9) >= 0 && isClear(k, storeOp, storeArg)) {
                skip.insert(at[k]); skip.insert(at[k + 1]); skip.insert(at[k + 2]);
                k += 2;
            }
        }
    }
}

// 3.8-3.10 SETUP_FINALLY guarding except handlers: the handler starts with DUP_TOP (typed) or POP_TOP x3 (bare)
static void ScanExceptSetups(PycRef<PycCode> code, PycModule* mod, const std::set<int>& skip,
                             std::set<int>& exceptSetups)
{
    if (mod->verCompare(3, 8) < 0 || mod->verCompare(3, 11) >= 0)
        return;
    PycBuffer src(code->code()->value(), code->code()->length());
    std::map<int, int> opAt, nextAt;
    std::vector<int> setups;
    int opcode, operand, pos = 0;
    std::map<int, int> targetOf;
    while (!src.atEof()) {
        int p = pos;
        bc_next(src, mod, opcode, operand, pos);
        opAt[p] = opcode;
        nextAt[p] = pos;
        if (opcode == Pyc::SETUP_FINALLY_A && !skip.count(p)) {
            setups.push_back(p);
            targetOf[p] = ast_relative_jump_target(mod, opcode, operand, pos, false);
        }
    }
    auto opAfter = [&](int at) {
        auto n = nextAt.find(at);
        return n == nextAt.end() || !opAt.count(n->second) ? -1 : opAt[n->second];
    };
    for (int p : setups) {
        int t = targetOf[p];
        if (!opAt.count(t))
            continue;
        bool bare = opAt[t] == Pyc::POP_TOP && opAfter(t) == Pyc::POP_TOP
                && opAfter(nextAt[t]) == Pyc::POP_TOP;
        if (opAt[t] == Pyc::DUP_TOP || bare)
            exceptSetups.insert(p);
    }
}

// Pre-3.11 try/finally: record handler starts; skip early-exit POP_BLOCK + CALL_FINALLY (3.8) or every inlined finally copy (3.9+)
static void ScanFinallyExits(PycRef<PycCode> code, PycModule* mod, const std::set<int>& exceptSetups,
                             std::set<int>& skip, std::set<int>& finallyHandlers)
{
    if (mod->verCompare(3, 11) >= 0)
        return;
    PycBuffer src(code->code()->value(), code->code()->length());
    std::vector<int> at, op, arg, next;
    int opcode, operand, pos = 0;
    while (!src.atEof()) {
        int p = pos;
        bc_next(src, mod, opcode, operand, pos);
        at.push_back(p); op.push_back(opcode); arg.push_back(operand); next.push_back(pos);
    }
    std::map<int, int> indexAt;
    for (size_t i = 0; i < at.size(); i++)
        indexAt[at[i]] = (int)i;
    auto absJump = [](int o) {
        return o == Pyc::JUMP_ABSOLUTE_A || o == Pyc::POP_JUMP_IF_FALSE_A || o == Pyc::POP_JUMP_IF_TRUE_A
            || o == Pyc::JUMP_IF_FALSE_OR_POP_A || o == Pyc::JUMP_IF_TRUE_OR_POP_A
            || o == Pyc::JUMP_IF_NOT_EXC_MATCH_A;
    };
    auto isSetup = [](int o) {
        return o == Pyc::SETUP_FINALLY_A || o == Pyc::SETUP_WITH_A || o == Pyc::SETUP_ASYNC_WITH_A;
    };
    auto skipPopBlocksBefore = [&](int k) {
        for (int b = k - 1; b >= 0 && op[b] == Pyc::POP_BLOCK; --b)
            skip.insert(at[b]);
    };
    for (size_t i = 0; i < at.size(); i++) {
        if (op[i] != Pyc::SETUP_FINALLY_A || exceptSetups.count(at[i]) || skip.count(at[i]))
            continue;
        int handler = ast_relative_jump_target(mod, op[i], arg[i], next[i], false);
        auto hi = indexAt.find(handler);
        if (hi == indexAt.end())
            continue;
        const int h = hi->second;
        if (mod->verCompare(3, 9) < 0) {
            finallyHandlers.insert(handler);
            if (mod->verCompare(3, 8) < 0)
                continue;
            for (int k = (int)i + 1; k < h; k++) {
                if (op[k] == Pyc::CALL_FINALLY_A
                        && ast_relative_jump_target(mod, op[k], arg[k], next[k], false) == handler) {
                    skip.insert(at[k]);
                    skipPopBlocksBefore(k);
                }
            }
            continue;
        }
        // Finally body = handler up to its RERAISE (nested setups in the body are left alone)
        int r = h;
        while (r < (int)op.size() && op[r] != Pyc::RERAISE && op[r] != Pyc::RERAISE_A && !isSetup(op[r]))
            r++;
        if (r >= (int)op.size() || isSetup(op[r]) || r == h)
            continue;
        const int len = r - h;
        auto sameAsFinally = [&](int k) {
            for (int j = 0; j < len; j++) {
                if (op[k + j] != op[h + j] || (!absJump(op[k + j]) && arg[k + j] != arg[h + j]))
                    return false;
            }
            return true;
        };
        finallyHandlers.insert(handler);
        for (int k = (int)i + 1; k + len <= h; k++) {
            if (op[k - 1] != Pyc::POP_BLOCK || !sameAsFinally(k))
                continue;
            for (int j = 0; j < len; j++)
                skip.insert(at[k + j]);
            skipPopBlocksBefore(k);
            // The normal exit then jumps over the handler to where the try statement resumes
            int after = k + len;
            if (after < h && op[after] == Pyc::JUMP_FORWARD_A
                    && ast_relative_jump_target(mod, op[after], arg[after], next[after], false) == next[r])
                skip.insert(at[after]);
            k += len - 1;
        }
    }
}

// 3.14+ builtin fast path: LOAD_GLOBAL f; COPY 1; LOAD_COMMON_CONSTANT f; IS_OP; POP_JUMP_IF_FALSE slow -> keep only the f(...) call
static void ScanBuiltinFastPaths(PycRef<PycCode> code, PycModule* mod, std::map<int, int>& skipUntil)
{
    if (mod->verCompare(3, 14) < 0)
        return;
    PycBuffer src(code->code()->value(), code->code()->length());
    std::vector<int> at, op, arg, next;
    int opcode, operand, pos = 0;
    while (!src.atEof()) {
        int p = pos;
        bc_next(src, mod, opcode, operand, pos);
        if (opcode == Pyc::CACHE)
            continue;
        at.push_back(p); op.push_back(opcode); arg.push_back(operand); next.push_back(pos);
    }
    for (size_t i = 0; i + 4 < op.size(); i++) {
        if (op[i] != Pyc::LOAD_GLOBAL_A || (arg[i] & 1) || op[i + 1] != Pyc::COPY_A || arg[i + 1] != 1
                || op[i + 2] != Pyc::LOAD_COMMON_CONSTANT_A || op[i + 3] != Pyc::IS_OP_A || arg[i + 3] != 0
                || op[i + 4] != Pyc::POP_JUMP_IF_FALSE_A)
            continue;
        int slow = ast_relative_jump_target(mod, op[i + 4], arg[i + 4], next[i + 4], false);
        if (slow > at[i + 1])
            skipUntil[at[i + 1]] = slow;
    }
}

// Target of the except handlers' exit jump (<= 3.8 layout): the jump right before END_FINALLY, else any POP_EXCEPT; JUMP
static int ast_handler_exit_target(PycRef<PycCode> code, PycModule* mod, int from, int endFinally)
{
    PycBuffer src(code->code()->value(), code->code()->length());
    if (!src.setPos(from))
        return 0;
    int opcode = 0, operand = 0, pos = from;
    int lastOp = -1, lastTarget = 0, prevOp = -1, popExceptTarget = 0;
    while (!src.atEof() && pos < endFinally) {
        bc_next(src, mod, opcode, operand, pos);
        int target = 0;
        if (opcode == Pyc::JUMP_FORWARD_A)
            target = ast_relative_jump_target(mod, opcode, operand, pos, false);
        else if (opcode == Pyc::JUMP_ABSOLUTE_A)
            target = mod->verCompare(3, 10) >= 0 ? operand * (int)sizeof(uint16_t) : operand;
        if (target && prevOp == Pyc::POP_EXCEPT)
            popExceptTarget = std::max(popExceptTarget, target);
        lastOp = opcode;
        lastTarget = target;
        prevOp = opcode;
    }
    if (pos != endFinally)
        return 0;
    if (lastOp == Pyc::JUMP_FORWARD_A || lastOp == Pyc::JUMP_ABSOLUTE_A)
        return lastTarget;
    return popExceptTarget;
}

static void ScanWhileLoops(PycRef<PycCode> code, PycModule* mod,
                           std::map<int,int>& whileGuardEnd,
                           std::set<int>& whileBackedges,
                           std::set<int>& whileLatchGuards,
                           std::map<int,int>& whileInvertedGuards,
                           std::map<int,int>& whileDupSkip,
                           std::set<int>& whileCondJumps,
                           std::map<int,int>& whileElseAt,
                           std::set<int>& whileAmbiguous)
{
    PycBuffer src(code->code()->value(), code->code()->length());
    int opcode, operand, pos = 0;
    std::vector<int> order;
    std::map<int,int> opAt, operAt, nextAt;
    while (!src.atEof()) {
        int p = pos;
        bc_next(src, mod, opcode, operand, pos);
        order.push_back(p);
        opAt[p] = opcode; operAt[p] = operand; nextAt[p] = pos;
    }
    std::map<int,int> instrEndingAt;   /* physical nextpos -> pos */
    for (int p : order)
        instrEndingAt[ast_next_instr_offset_after_caches(mod, opAt[p], nextAt[p])] = p;

    auto isCondBack = [](int op){
        return op == Pyc::POP_JUMP_BACKWARD_IF_TRUE_A
            || op == Pyc::POP_JUMP_BACKWARD_IF_FALSE_A
            || op == Pyc::POP_JUMP_BACKWARD_IF_NONE_A
            || op == Pyc::POP_JUMP_BACKWARD_IF_NOT_NONE_A;
    };
    auto isFwdGuard = [](int op){
        return op == Pyc::POP_JUMP_IF_FALSE_A
            || op == Pyc::POP_JUMP_IF_TRUE_A
            || op == Pyc::POP_JUMP_IF_NONE_A
            || op == Pyc::POP_JUMP_IF_NOT_NONE_A
            || op == Pyc::POP_JUMP_FORWARD_IF_FALSE_A
            || op == Pyc::POP_JUMP_FORWARD_IF_TRUE_A
            || op == Pyc::POP_JUMP_FORWARD_IF_NONE_A
            || op == Pyc::POP_JUMP_FORWARD_IF_NOT_NONE_A
            || op == Pyc::INSTRUMENTED_POP_JUMP_IF_FALSE_A
            || op == Pyc::INSTRUMENTED_POP_JUMP_IF_TRUE_A
            || op == Pyc::INSTRUMENTED_POP_JUMP_IF_NONE_A
            || op == Pyc::INSTRUMENTED_POP_JUMP_IF_NOT_NONE_A;
    };
    // 3.8/3.9 top-tested while: S: cond; POP_JUMP_IF_* T; body; JUMP_ABSOLUTE S; T:
    if (mod->verCompare(3, 8) >= 0 && mod->verCompare(3, 10) < 0) {
        // Only the last back-edge to a head closes the loop; earlier ones are continues
        std::map<int, int> lastBack;
        for (int b : order) {
            if (opAt[b] == Pyc::JUMP_ABSOLUTE_A && operAt[b] < b)
                lastBack[operAt[b]] = b;
        }
        for (int b : order) {
            if (opAt[b] != Pyc::JUMP_ABSOLUTE_A || lastBack[operAt[b]] != b)
                continue;
            int end = nextAt[b], loop_start = operAt[b];
            auto head = opAt.find(loop_start);
            if (loop_start >= b || head == opAt.end() || head->second == Pyc::FOR_ITER_A
                    || head->second == Pyc::SETUP_FINALLY_A)
                continue;
            // A handler exit (POP_EXCEPT; JUMP_ABSOLUTE) is not a while back-edge
            auto prev = instrEndingAt.find(b);
            if (prev != instrEndingAt.end() && opAt[prev->second] == Pyc::POP_EXCEPT)
                continue;
            // The header's first conditional jump must leave the loop; compound conditions are left to the if logic
            // (the exit may be threaded through an unconditional jump right at the loop end)
            auto atEnd = opAt.find(end);
            int threaded = atEnd != opAt.end() && atEnd->second == Pyc::JUMP_ABSOLUTE_A ? operAt[end] : end;
            int guard = -1, exits = 0;
            bool seenCond = false;
            for (int g : order) {
                if (g < loop_start || g >= b)
                    continue;
                bool cond = isFwdGuard(opAt[g]) || opAt[g] == Pyc::JUMP_IF_FALSE_OR_POP_A
                        || opAt[g] == Pyc::JUMP_IF_TRUE_OR_POP_A;
                bool leaves = operAt[g] == end || operAt[g] == threaded;
                if (cond && !seenCond && isFwdGuard(opAt[g]) && leaves)
                    guard = g;
                seenCond = seenCond || cond;
                if (cond && leaves)
                    exits++;
            }
            // Every leaving jump shares the back-edge fallthrough: while A and B, not a bare if
            bool pureAnd = exits >= 1;
            if (exits > 1) {
                for (int g : order) {
                    if (g < loop_start || g >= b)
                        continue;
                    bool cond = isFwdGuard(opAt[g]) || opAt[g] == Pyc::JUMP_IF_FALSE_OR_POP_A
                            || opAt[g] == Pyc::JUMP_IF_TRUE_OR_POP_A;
                    if (cond && (operAt[g] == end || operAt[g] == threaded) && operAt[g] != end)
                        pureAnd = false;
                }
            }
            // Compound `and` is a while only when the header stores a walrus; a plain if must stay an if
            bool headerWalrus = false;
            if (exits > 1 && guard > loop_start) {
                for (int g : order) {
                    if (g <= loop_start || g >= guard)
                        continue;
                    bool store = opAt[g] == Pyc::STORE_FAST_A || opAt[g] == Pyc::STORE_NAME_A
                            || opAt[g] == Pyc::STORE_GLOBAL_A || opAt[g] == Pyc::STORE_DEREF_A
                            || opAt[g] == Pyc::STORE_ATTR_A || opAt[g] == Pyc::STORE_SUBSCR;
                    if (!store)
                        continue;
                    int prev = -1;
                    for (int p : order) {
                        if (p >= g)
                            break;
                        if (p >= loop_start)
                            prev = p;
                    }
                    if (prev >= 0 && opAt[prev] == Pyc::DUP_TOP)
                        headerWalrus = true;
                }
            }
            if (guard >= 0 && (exits == 1 || (pureAnd && headerWalrus))) {
                whileGuardEnd[guard] = end;
                whileBackedges.insert(b);
            }
        }
        return;
    }

    // 3.10 while: forward POP_JUMP_IF_* into the loop, body, then a backward POP_JUMP_IF_* to the body
    if (mod->verCompare(3, 10) == 0) {
        auto isPopJump = [](int op) {
            return op == Pyc::POP_JUMP_IF_TRUE_A || op == Pyc::POP_JUMP_IF_FALSE_A;
        };
        auto absJump = [&](int p) {
            return operAt[p] * (int)sizeof(uint16_t);
        };
        // Stop the condition walk at a statement, not at an unrecognized expression opcode
        auto isBoundary = [](int op) {
            return op == Pyc::POP_TOP || op == Pyc::STORE_NAME_A || op == Pyc::STORE_FAST_A
                || op == Pyc::STORE_GLOBAL_A || op == Pyc::STORE_DEREF_A || op == Pyc::STORE_ATTR_A
                || op == Pyc::STORE_SUBSCR || op == Pyc::STORE_ANNOTATION_A
                || op == Pyc::DELETE_NAME_A || op == Pyc::DELETE_FAST_A || op == Pyc::DELETE_GLOBAL_A
                || op == Pyc::DELETE_ATTR_A || op == Pyc::DELETE_SUBSCR || op == Pyc::DELETE_DEREF_A
                || op == Pyc::RETURN_VALUE || op == Pyc::RAISE_VARARGS_A
                || op == Pyc::RERAISE || op == Pyc::RERAISE_A
                || op == Pyc::POP_BLOCK || op == Pyc::POP_EXCEPT
                || op == Pyc::SETUP_FINALLY_A || op == Pyc::SETUP_WITH_A || op == Pyc::SETUP_ASYNC_WITH_A
                || op == Pyc::SETUP_EXCEPT_A || op == Pyc::JUMP_FORWARD_A || op == Pyc::JUMP_ABSOLUTE_A
                || op == Pyc::JUMP_IF_NOT_EXC_MATCH_A || op == Pyc::JUMP_IF_FALSE_OR_POP_A
                || op == Pyc::JUMP_IF_TRUE_OR_POP_A || op == Pyc::FOR_ITER_A || op == Pyc::GET_ITER
                || op == Pyc::YIELD_VALUE || op == Pyc::YIELD_FROM || op == Pyc::PRINT_EXPR
                || op == Pyc::IMPORT_STAR;
        };
        std::map<int, int> indexOf;
        for (size_t i = 0; i < order.size(); i++)
            indexOf[order[i]] = (int)i;
        auto prevOf = [&](int p) -> int {
            std::map<int, int>::iterator found = indexOf.find(p);
            if (found == indexOf.end() || found->second <= 0)
                return -1;
            return order[found->second - 1];
        };
        const char* bytes = code->code()->value();
        int codeLen = code->code()->length();
        // [from, to) is one or more copies of the returning block that starts at to
        auto duplicateExit = [&](int from, int to) {
            if (to <= from || to > codeLen || bytes == nullptr)
                return false;
            int span = to - from;
            for (int elen = 2; elen <= span && elen <= 16 && to + elen <= codeLen; elen += 2) {
                if (span % elen != 0)
                    continue;
                bool match = true;
                for (int at = from; match && at < to; at += elen)
                    match = memcmp(bytes + at, bytes + to, elen) == 0;
                if (!match)
                    continue;
                int last = -1;
                for (int p : order) {
                    if (p >= to && p < to + elen)
                        last = p;
                }
                if (last >= 0 && opAt[last] == Pyc::RETURN_VALUE)
                    return true;
            }
            return false;
        };
        // Two jumps may land on different copies of the same return; that is still one exit
        auto returnSpan = [&](int at) -> int {
            for (int p : order) {
                if (p < at)
                    continue;
                if (p > at + 12)
                    return 0;
                int op = opAt[p];
                if (op == Pyc::CACHE)
                    continue;
                if (op == Pyc::LOAD_CONST_A)
                    continue;
                if (op == Pyc::RETURN_VALUE)
                    return nextAt[p] > at ? nextAt[p] - at : 0;
                return 0;
            }
            return 0;
        };
        // Copies of one return need not leave another full copy after the last one
        auto sameExitBlock = [&](int target, int exit) {
            if (target == exit)
                return true;
            int span = returnSpan(target);
            if (span < 2 || span != returnSpan(exit) || bytes == nullptr)
                return false;
            if (target < 0 || exit < 0 || target + span > codeLen || exit + span > codeLen)
                return false;
            return memcmp(bytes + target, bytes + exit, span) == 0;
        };
        // DUP_TOP; STORE a few instructions before the jump is a walrus in this test
        auto nearWalrus = [&](int at) {
            int prev = prevOf(at);
            for (int steps = 0; prev >= 0 && steps < 8; steps++) {
                int op = opAt[prev];
                bool store = op == Pyc::STORE_FAST_A || op == Pyc::STORE_NAME_A
                        || op == Pyc::STORE_GLOBAL_A || op == Pyc::STORE_DEREF_A
                        || op == Pyc::STORE_ATTR_A || op == Pyc::STORE_SUBSCR;
                int before = prevOf(prev);
                if (store && before >= 0 && opAt[before] == Pyc::DUP_TOP)
                    return true;
                if (isBoundary(op))
                    return false;
                prev = prevOf(prev);
            }
            return false;
        };
        std::map<int, int> lastBack;
        for (int b : order) {
            if (!isPopJump(opAt[b]))
                continue;
            int target = absJump(b);
            if (target < b && opAt.count(target))
                lastBack[target] = b;
        }
        for (std::map<int, int>::iterator back = lastBack.begin(); back != lastBack.end(); ++back) {
            int body = back->first;
            int b = back->second;
            std::map<int, int>::iterator git = instrEndingAt.find(body);
            if (git == instrEndingAt.end() || !isPopJump(opAt[git->second]))
                continue;
            int guard = git->second;
            int exit = absJump(guard);
            int fall = nextAt[b];
            if (exit < fall)
                continue;
            // Conditional jumps of this test only. A jump into the test stays
            // (`(a or b) and c`); a jump to another loop's exit does not.
            std::vector<int> chain;
            chain.push_back(guard);
            for (int scan = prevOf(guard); scan >= 0; scan = prevOf(scan)) {
                int op = opAt[scan];
                if (isPopJump(op)) {
                    int target = absJump(scan);
                    if (target < scan)
                        break;
                    bool inCond = target > scan && target < body;
                    // Only a walrus test may treat a copied return as the same exit
                    bool copiedExit = sameExitBlock(target, exit) && nearWalrus(scan);
                    if (target != exit && target != body && !inCond && !copiedExit)
                        break;
                    chain.push_back(scan);
                    continue;
                }
                // DUP_TOP; STORE is a walrus inside the condition, not a statement boundary
                bool walrusStore = (op == Pyc::STORE_FAST_A || op == Pyc::STORE_NAME_A
                        || op == Pyc::STORE_GLOBAL_A || op == Pyc::STORE_DEREF_A
                        || op == Pyc::STORE_ATTR_A || op == Pyc::STORE_SUBSCR);
                int prev = prevOf(scan);
                if (isBoundary(op) && !(walrusStore && prev >= 0 && opAt[prev] == Pyc::DUP_TOP))
                    break;
            }
            bool pureAnd = true;
            bool pureOr = chain.size() == 2;
            for (size_t i = 0; i < chain.size(); i++) {
                int target = absJump(chain[i]);
                bool last = i == 0; // chain is stored from the guard backward
                if (target != exit && !(sameExitBlock(target, exit) && nearWalrus(chain[i])))
                    pureAnd = false;
                if (last) {
                    if (target != exit)
                        pureOr = false;
                } else if (target != body || opAt[chain[i]] != Pyc::POP_JUMP_IF_TRUE_A) {
                    pureOr = false;
                }
            }
            bool single = chain.size() == 1 && absJump(chain[0]) == exit;
            // Existing and/or folding only matches all-to-exit, or one jump to the body plus one to the exit
            if (!(pureAnd || pureOr || single)) {
                whileAmbiguous.insert(chain.back());
                continue;
            }
            int first = chain.back();
            int firstTarget = absJump(first);
            // A walrus `and` may jump at a nearer copy of the far return
            whileGuardEnd[first] = (sameExitBlock(firstTarget, exit) && nearWalrus(first))
                    ? exit : firstTarget;
            for (size_t i = 0; i + 1 < chain.size(); i++)
                whileCondJumps.insert(chain[i]);
            whileBackedges.insert(b);
            for (int scan = prevOf(b); scan > body; scan = prevOf(scan)) {
                int op = opAt[scan];
                if (isPopJump(op)) {
                    int target = absJump(scan);
                    if (target == body || target == exit || target >= fall)
                        whileLatchGuards.insert(scan);
                    else
                        break;
                    continue;
                }
                // DUP_TOP; STORE is a walrus inside the condition, not a statement boundary
                bool walrusStore = (op == Pyc::STORE_FAST_A || op == Pyc::STORE_NAME_A
                        || op == Pyc::STORE_GLOBAL_A || op == Pyc::STORE_DEREF_A
                        || op == Pyc::STORE_ATTR_A || op == Pyc::STORE_SUBSCR);
                int prev = prevOf(scan);
                if (isBoundary(op) && !(walrusStore && prev >= 0 && opAt[prev] == Pyc::DUP_TOP))
                    break;
            }
            if (exit > fall && duplicateExit(fall, exit))
                whileDupSkip[b] = exit;
            // A jump from the body past the fall-through is a break over the else clause
            if (exit == fall) {
                int elseEnd = -1;
                for (int p : order) {
                    if (p < body || p >= b)
                        continue;
                    int op = opAt[p];
                    int target = -1;
                    if (op == Pyc::JUMP_ABSOLUTE_A)
                        target = absJump(p);
                    else if (op == Pyc::JUMP_FORWARD_A)
                        target = ast_relative_jump_target(mod, op, operAt[p], nextAt[p], false);
                    if (target > exit && (elseEnd < 0 || target < elseEnd))
                        elseEnd = target;
                }
                if (elseEnd > exit)
                    whileElseAt[b] = elseEnd;
            }
        }
        return;
    }

    // Exit-block duplication (3.11+): [end, target) repeats the short returning block at target
    auto dupExit = [&](int end, int target) {
        int len = target - end;
        if (len <= 0 || len > 24 || target + len > code->code()->length())
            return false;
        const char* bytes = code->code()->value();
        if (memcmp(bytes + end, bytes + target, len) != 0)
            return false;
        int last = -1;
        for (int p : order) {
            if (p >= end && p < target && opAt[p] != Pyc::CACHE)
                last = p;
        }
        return last >= 0 && (opAt[last] == Pyc::RETURN_VALUE || opAt[last] == Pyc::RETURN_CONST_A);
    };
    auto returnSpan = [&](int at) -> int {
        for (int p : order) {
            if (p < at)
                continue;
            if (p > at + 12)
                return 0;
            int op = opAt[p];
            if (op == Pyc::CACHE || op == Pyc::NOT_TAKEN || op == Pyc::INSTRUMENTED_NOT_TAKEN_A)
                continue;
            if (op == Pyc::LOAD_CONST_A)
                continue;
            if (op == Pyc::RETURN_VALUE || op == Pyc::RETURN_CONST_A
                    || op == Pyc::INSTRUMENTED_RETURN_VALUE_A
                    || op == Pyc::INSTRUMENTED_RETURN_CONST_A)
                return nextAt[p] > at ? nextAt[p] - at : 0;
            return 0;
        }
        return 0;
    };
    auto sameReturn = [&](int a, int b) {
        if (a == b)
            return true;
        int span = returnSpan(a);
        if (span < 2 || span != returnSpan(b) || code->code() == nullptr)
            return false;
        const char* bytes = code->code()->value();
        int len = code->code()->length();
        if (bytes == nullptr || a < 0 || b < 0 || a + span > len || b + span > len)
            return false;
        return memcmp(bytes + a, bytes + b, span) == 0;
    };

    for (int b : order) {
        if (!isCondBack(opAt[b]))
            continue;
        int end = ast_next_instr_offset_after_caches(mod, opAt[b], nextAt[b]);
        int loop_start = end - operAt[b] * 2;   /* backward target */
        if (loop_start < 0 || loop_start >= b)
            continue;
        auto git = instrEndingAt.find(loop_start);
        if (git == instrEndingAt.end())
            continue;
        int guard = git->second;
        if (!isFwdGuard(opAt[guard]))
            continue;
        int guard_target = ast_next_instr_offset_after_caches(
                mod, opAt[guard], nextAt[guard]) + operAt[guard] * 2;
        bool copiedReturn = guard_target != end && !dupExit(end, guard_target)
                && sameReturn(end, guard_target);
        bool dup = guard_target != end && (dupExit(end, guard_target) || copiedReturn);
        if (guard_target != end && !dup)            /* guard must skip to loop end */
            continue;
        int useGuard = guard;
        // Earlier jumps to copies of this return are the rest of `while A and B`
        if (copiedReturn) {
            int scan = guard;
            while (guard - scan < 80) {
                int prev = -1;
                for (int p : order) {
                    if (p >= scan)
                        break;
                    if (opAt[p] == Pyc::CACHE || opAt[p] == Pyc::NOT_TAKEN
                            || opAt[p] == Pyc::INSTRUMENTED_NOT_TAKEN_A)
                        continue;
                    prev = p;
                }
                if (prev < 0)
                    break;
                int op = opAt[prev];
                bool store = op == Pyc::STORE_FAST_A || op == Pyc::STORE_NAME_A
                        || op == Pyc::STORE_GLOBAL_A || op == Pyc::STORE_DEREF_A
                        || op == Pyc::STORE_ATTR_A || op == Pyc::STORE_SUBSCR;
                if (store) {
                    int before = -1;
                    for (int p : order) {
                        if (p >= prev)
                            break;
                        if (opAt[p] == Pyc::CACHE || opAt[p] == Pyc::NOT_TAKEN)
                            continue;
                        before = p;
                    }
                    if (before >= 0 && (opAt[before] == Pyc::DUP_TOP || opAt[before] == Pyc::COPY_A)) {
                        scan = prev;
                        continue;
                    }
                    break;
                }
                if (isFwdGuard(op)) {
                    int tgt = ast_next_instr_offset_after_caches(mod, op, nextAt[prev]) + operAt[prev] * 2;
                    if (tgt == guard_target || sameReturn(tgt, guard_target)) {
                        whileCondJumps.insert(useGuard);
                        useGuard = prev;
                        scan = prev;
                        continue;
                    }
                    break;
                }
                if (op == Pyc::POP_TOP || op == Pyc::RETURN_VALUE || op == Pyc::RETURN_CONST_A
                        || op == Pyc::JUMP_FORWARD_A || op == Pyc::JUMP_BACKWARD_A)
                    break;
                scan = prev;
            }
        }
        whileGuardEnd[useGuard] = guard_target;
        whileBackedges.insert(b);
        if (dup)
            whileDupSkip[b] = guard_target;
    }

    /* Python 3.13+ may emit a top-tested while as a forward conditional guard
       plus an unconditional JUMP_BACKWARD.  In 3.13 the back-edge targets the
       point immediately after the entry guard, so prefer that guard's direct
       predecessor.  Python 3.14 also has layouts where the guard starts at the
       target; retain the bounded forward search as a fallback for those. */
    // 3.12 uses the same guard plus JUMP_BACKWARD layout
    if (mod->verCompare(3, 12) >= 0) {
        for (int b : order) {
            // JUMP_BACKWARD_NO_INTERRUPT is a handler exit or send loop, never a while back-edge
            if (opAt[b] != Pyc::JUMP_BACKWARD_A
                    && opAt[b] != Pyc::INSTRUMENTED_JUMP_BACKWARD_A)
                continue;
            int end = ast_next_instr_offset_after_caches(mod, opAt[b], nextAt[b]);
            int loop_start = end - operAt[b] * 2;
            if (loop_start < 0 || loop_start >= b)
                continue;
            // A jump back to FOR_ITER is a for-loop continue, not a while back-edge
            auto target = opAt.find(loop_start);
            if (target != opAt.end() && (target->second == Pyc::FOR_ITER_A
                        || target->second == Pyc::INSTRUMENTED_FOR_ITER_A))
                continue;
            // 3.12 leaves an exception handler with a plain JUMP_BACKWARD after POP_EXCEPT
            int prevReal = -1;
            for (int candidate : order) {
                if (candidate >= b)
                    break;
                if (opAt[candidate] != Pyc::CACHE && opAt[candidate] != Pyc::NOT_TAKEN)
                    prevReal = candidate;
            }
            if (prevReal >= 0 && opAt[prevReal] == Pyc::POP_EXCEPT)
                continue;

            auto recordGuard = [&](int guard) {
                if (!isFwdGuard(opAt[guard]))
                    return false;
                int guard_target = ast_next_instr_offset_after_caches(
                        mod, opAt[guard], nextAt[guard]) + operAt[guard] * 2;
                if (guard_target < end || guard_target <= b)
                    return false;
                whileGuardEnd[guard] = guard_target;
                if (guard_target == end) {
                    whileBackedges.insert(b);
                } else if (dupExit(end, guard_target)) {
                    whileBackedges.insert(b);
                    whileDupSkip[b] = guard_target;
                }
                return true;
            };

            int predecessorGuard = -1;
            for (auto it = order.rbegin(); it != order.rend(); ++it) {
                int candidate = *it;
                if (candidate >= loop_start)
                    continue;
                if (ast_next_instr_offset_after_caches(
                            mod, opAt[candidate], nextAt[candidate]) != loop_start)
                    continue;
                if (isFwdGuard(opAt[candidate])) {
                    predecessorGuard = candidate;
                    break;
                }
            }
            if (predecessorGuard >= 0 && recordGuard(predecessorGuard))
            {
                for (auto it = order.rbegin(); it != order.rend(); ++it) {
                    int latch = *it;
                    if (latch >= b)
                        continue;
                    if (latch < loop_start || b - latch > 64)
                        break;
                    if (!isFwdGuard(opAt[latch]))
                        continue;
                    int latchTarget = ast_next_instr_offset_after_caches(
                            mod, opAt[latch], nextAt[latch]) + operAt[latch] * 2;
                    if (latchTarget == end)
                        whileLatchGuards.insert(latch);
                    break;
                }
                continue;
            }

            // 3.14 also has layouts where the guard starts at the back-edge target
            // (only expression code may precede it: a completed statement means an `if` inside `while True`)
            bool found = false;
            if (mod->verCompare(3, 14) >= 0) {
                int prevOp = -1;
                for (int guard : order) {
                    if (guard < loop_start)
                        continue;
                    if (guard >= b || guard > loop_start + 64)
                        break;
                    int op = opAt[guard];
                    bool store = op == Pyc::STORE_FAST_A || op == Pyc::STORE_NAME_A || op == Pyc::STORE_GLOBAL_A
                            || op == Pyc::STORE_DEREF_A || op == Pyc::STORE_ATTR_A || op == Pyc::STORE_SUBSCR;
                    if (op == Pyc::POP_TOP || op == Pyc::DELETE_FAST_A || op == Pyc::DELETE_NAME_A
                            || (store && prevOp != Pyc::COPY_A))
                        break;
                    if (op != Pyc::CACHE)
                        prevOp = op;
                    if (recordGuard(guard)) {
                        found = true;
                        break;
                    }
                }
            }

            // While ending its enclosing loop body: `cond; POP_JUMP_IF_TRUE body; JUMP exit; body:` enters on true
            // (3.12/3.13: the back-edge targets the body; 3.14+: it targets the condition before the guard)
            if (predecessorGuard < 0 && !found) {
                std::vector<int> real;
                for (int candidate : order) {
                    if (opAt[candidate] != Pyc::CACHE && opAt[candidate] != Pyc::NOT_TAKEN
                            && opAt[candidate] != Pyc::INSTRUMENTED_NOT_TAKEN_A)
                        real.push_back(candidate);
                }
                // The loop header's first conditional jump
                int firstCond = -1;
                for (int candidate : real) {
                    if (candidate >= loop_start && firstCond < 0 && isFwdGuard(opAt[candidate]))
                        firstCond = candidate;
                }
                int guard = -1, bodyStart = -1;
                for (size_t i = 0; i + 1 < real.size(); i++) {
                    int g = real[i], x = real[i + 1];
                    if (!isFwdGuard(opAt[g]) || (opAt[x] != Pyc::JUMP_BACKWARD_A && opAt[x] != Pyc::JUMP_FORWARD_A))
                        continue;
                    int after = ast_next_instr_offset_after_caches(mod, opAt[x], nextAt[x]);
                    int target = ast_next_instr_offset_after_caches(mod, opAt[g], nextAt[g]) + operAt[g] * 2;
                    if (target != after)
                        continue;
                    // The skipped jump must leave this loop (outer loop head or past the end)
                    int exitTo = opAt[x] == Pyc::JUMP_BACKWARD_A ? after - operAt[x] * 2 : after + operAt[x] * 2;
                    if (x == b || (exitTo >= loop_start && exitTo < end))
                        continue;
                    bool bodyHead = after == loop_start;
                    bool condHead = g == firstCond && g < loop_start + 64 && g < b;
                    bool handlerInside = false;
                    for (int p : order) {
                        if (p >= std::min(g, loop_start) && p < b && opAt[p] == Pyc::PUSH_EXC_INFO)
                            handlerInside = true;
                    }
                    if (handlerInside)
                        break;
                    if (bodyHead || condHead) {
                        guard = g;
                        bodyStart = after;
                        break;
                    }
                }
                if (guard >= 0) {
                    whileGuardEnd[guard] = end;
                    whileBackedges.insert(b);
                    whileInvertedGuards[guard] = bodyStart;
                    for (auto it = order.rbegin(); it != order.rend(); ++it) {
                        int latch = *it;
                        if (latch >= b)
                            continue;
                        if (latch < bodyStart || b - latch > 64)
                            break;
                        if (!isFwdGuard(opAt[latch]))
                            continue;
                        if (ast_next_instr_offset_after_caches(mod, opAt[latch], nextAt[latch])
                                + operAt[latch] * 2 == end)
                            whileLatchGuards.insert(latch);
                        break;
                    }
                    continue;
                }
            }

        }
    }
}

// `while True:` (3.8+): an unconditional back-edge to a head no other loop owns; the last one closes the loop
static void ScanInfiniteLoops(PycRef<PycCode> code, PycModule* mod,
                              const std::vector<PycExceptionTableEntry>& entries,
                              std::set<int>& whileBackedges, std::map<int,int>& whileTrueAt)
{
    PycBuffer src(code->code()->value(), code->code()->length());
    int opcode, operand, pos = 0;
    std::vector<int> order;
    std::map<int,int> opAt, operAt, nextAt;
    while (!src.atEof()) {
        int p = pos;
        bc_next(src, mod, opcode, operand, pos);
        if (opcode == Pyc::CACHE)
            continue;
        order.push_back(p);
        opAt[p] = opcode; operAt[p] = operand; nextAt[p] = ast_next_instr_offset_after_caches(mod, opcode, pos);
    }
    auto backTarget = [&](int b) {
        if (opAt[b] == Pyc::JUMP_ABSOLUTE_A && mod->verCompare(3, 11) < 0)
            return mod->verCompare(3, 10) >= 0 ? operAt[b] * 2 : operAt[b];
        if (opAt[b] == Pyc::JUMP_BACKWARD_A && mod->verCompare(3, 11) >= 0)
            return nextAt[b] - operAt[b] * 2;
        return -1;
    };
    auto isCond = [&](int op) {
        return op == Pyc::POP_JUMP_IF_FALSE_A || op == Pyc::POP_JUMP_IF_TRUE_A
            || op == Pyc::POP_JUMP_IF_NONE_A || op == Pyc::POP_JUMP_IF_NOT_NONE_A
            || op == Pyc::POP_JUMP_FORWARD_IF_FALSE_A || op == Pyc::POP_JUMP_FORWARD_IF_TRUE_A
            || op == Pyc::POP_JUMP_FORWARD_IF_NONE_A || op == Pyc::POP_JUMP_FORWARD_IF_NOT_NONE_A
            || op == Pyc::JUMP_IF_FALSE_OR_POP_A || op == Pyc::JUMP_IF_TRUE_OR_POP_A;
    };
    auto condTarget = [&](int g) {
        bool relative = mod->verCompare(3, 12) >= 0 || opAt[g] == Pyc::POP_JUMP_FORWARD_IF_FALSE_A
                || opAt[g] == Pyc::POP_JUMP_FORWARD_IF_TRUE_A || opAt[g] == Pyc::POP_JUMP_FORWARD_IF_NONE_A
                || opAt[g] == Pyc::POP_JUMP_FORWARD_IF_NOT_NONE_A
                || (mod->verCompare(3, 11) >= 0 && (opAt[g] == Pyc::JUMP_IF_FALSE_OR_POP_A
                        || opAt[g] == Pyc::JUMP_IF_TRUE_OR_POP_A));
        if (relative)
            return nextAt[g] + operAt[g] * 2;
        return mod->verCompare(3, 10) >= 0 ? operAt[g] * 2 : operAt[g];
    };
    std::set<int> heads;
    for (int b : whileBackedges) {
        if (opAt.count(b) && (opAt[b] == Pyc::JUMP_ABSOLUTE_A || opAt[b] == Pyc::JUMP_BACKWARD_A))
            heads.insert(backTarget(b));
        else if (opAt.count(b) && mod->verCompare(3, 10) == 0
                && (opAt[b] == Pyc::POP_JUMP_IF_TRUE_A || opAt[b] == Pyc::POP_JUMP_IF_FALSE_A))
            heads.insert(operAt[b] * (int)sizeof(uint16_t));
        else if (opAt.count(b))
            heads.insert(nextAt[b] - operAt[b] * 2);
    }
    // 3.12+ places exception handlers behind the code; their exits are not loop back-edges
    int handlerRegion = INT_MAX;
    if (mod->verCompare(3, 12) >= 0) {
        for (const auto& entry : entries)
            handlerRegion = std::min(handlerRegion, entry.target);
    }
    std::map<int, int> closing;
    int prev = -1;
    for (int b : order) {
        int L = backTarget(b);
        bool handlerExit = prev >= 0 && opAt[prev] == Pyc::POP_EXCEPT;
        prev = b;
        if (L < 0 || L >= b || b >= handlerRegion || handlerExit || whileBackedges.count(b) || heads.count(L))
            continue;
        auto head = opAt.find(L);
        if (head == opAt.end() || head->second == Pyc::FOR_ITER_A || head->second == Pyc::SETUP_FINALLY_A
                || head->second == Pyc::GET_ANEXT)
            continue;
        closing[L] = std::max(closing[L], b);
    }
    for (const auto& c : closing) {
        int L = c.first, b = c.second, exit = nextAt[b];
        auto atExit = opAt.find(exit);
        int threaded = atExit != opAt.end() && (atExit->second == Pyc::JUMP_ABSOLUTE_A
                || atExit->second == Pyc::JUMP_BACKWARD_A || atExit->second == Pyc::JUMP_FORWARD_A)
                ? (atExit->second == Pyc::JUMP_FORWARD_A ? nextAt[exit] + operAt[exit] * (mod->verCompare(3, 10) >= 0 ? 2 : 1)
                        : backTarget(exit))
                : exit;
        // A loop whose header test leaves it is a conditional loop the while scan did not recognise
        // (a test after a completed statement is an `if ...: break` inside `while True`)
        bool conditional = false;
        int prevOp = -1;
        for (int g : order) {
            if (g < L || g >= b)
                continue;
            int op = opAt[g];
            bool store = op == Pyc::STORE_FAST_A || op == Pyc::STORE_NAME_A || op == Pyc::STORE_GLOBAL_A
                    || op == Pyc::STORE_DEREF_A || op == Pyc::STORE_ATTR_A || op == Pyc::STORE_SUBSCR;
            if (op == Pyc::POP_TOP || (store && prevOp != Pyc::COPY_A && prevOp != Pyc::DUP_TOP))
                break;
            prevOp = op;
            if (isCond(op)) {
                int t = condTarget(g);
                conditional = t == exit || t == threaded || t > b;
                break;
            }
        }
        if (conditional)
            continue;
        // Another conditional back-edge to the head means a bottom-tested loop
        bool condBack = false;
        for (int g : order) {
            if ((opAt[g] == Pyc::POP_JUMP_BACKWARD_IF_TRUE_A || opAt[g] == Pyc::POP_JUMP_BACKWARD_IF_FALSE_A
                        || opAt[g] == Pyc::POP_JUMP_BACKWARD_IF_NONE_A || opAt[g] == Pyc::POP_JUMP_BACKWARD_IF_NOT_NONE_A)
                    && nextAt[g] - operAt[g] * 2 == L)
                condBack = true;
        }
        if (condBack)
            continue;
        whileTrueAt[L] = exit;
        whileBackedges.insert(b);
    }
}

/* Python 3.11 chained-comparison pre-pass. `a == b == c` compiles to two
   COMPARE_OP/POP_JUMP_FORWARD_IF_FALSE halves sharing the middle operand
   (duplicated via SWAP/COPY), followed by a trailer:
        JUMP_FORWARD body      (both comparisons true -> run the body)
   tramp:
        POP_TOP                (false path: discard the leftover middle operand)
        JUMP_FORWARD exit
   body:
   The first half's POP_JUMP targets `tramp`, the second's targets `exit`; the
   default merge logic sees different targets and joins them with `or` instead of
   `and`, leaving the body outside the if. Record: the trailer's leading
   JUMP_FORWARD (to skip over the trampoline) and the trampoline POP_TOP position
   mapped to its real exit, so a POP_JUMP landing on the trampoline can be
   resolved to the exit and the two halves merge with `and`. */
static void ScanChainedCompare(PycRef<PycCode> code, PycModule* mod,
                               std::map<int,int>& chainSkipJumps,
                               std::map<int,int>& trampolineExit)
{
    PycBuffer src(code->code()->value(), code->code()->length());
    int opcode, operand, pos = 0;
    std::vector<int> order;
    std::map<int,int> opAt, operAt, nextAt;
    while (!src.atEof()) {
        int p = pos;
        bc_next(src, mod, opcode, operand, pos);
        order.push_back(p);
        opAt[p] = opcode; operAt[p] = operand; nextAt[p] = pos;
    }
    auto nextRealInstruction = [&opAt, &nextAt](int at) {
        auto next = nextAt.find(at);
        if (next == nextAt.end())
            return -1;
        int p = next->second;
        while (p >= 0 && opAt[p] == Pyc::CACHE) {
            next = nextAt.find(p);
            if (next == nextAt.end())
                return -1;
            p = next->second;
        }
        return p;
    };
    for (int j : order) {
        if (opAt[j] != Pyc::JUMP_FORWARD_A)
            continue;
        int pop = nextRealInstruction(j);
        int body = pop >= 0 ? nextRealInstruction(pop) : -1;
        int target = ast_next_instr_offset_after_caches(
                mod, opAt[j], nextAt[j]) + operAt[j] * 2;
        if (pop >= 0 && body >= 0 && opAt[pop] == Pyc::POP_TOP
                && target == body) {
            /* Chained comparisons retain the middle operand for the second
               comparison. On the failed first half this jump skips the
               POP_TOP cleanup and enters the real body. It is not an else
               boundary, so consume only the synthetic cleanup. */
            chainSkipJumps[j] = body;
        }
    }
    for (size_t i = 0; i + 2 < order.size(); i++) {
        int j = order[i], p = order[i + 1], q = order[i + 2];
        if (opAt[j] == Pyc::JUMP_FORWARD_A
                && opAt[p] == Pyc::POP_TOP
                && opAt[q] == Pyc::JUMP_FORWARD_A) {
            int bodyTarget = nextAt[j] + operAt[j] * 2;
            int exitTarget = nextAt[q] + operAt[q] * 2;
            /* the trailer's leading JUMP_FORWARD must jump just past the
               trampoline (to the body that begins after q) */
            if (bodyTarget == nextAt[q]) {
                chainSkipJumps[j] = bodyTarget;
                trampolineExit[p] = exitTarget;
            }
        }
    }
}

// Length of a 3.10 while-exit block small enough for CPython to copy (at most 4 instructions)
static int ast_py310_exit_block_len(PycRef<PycCode> code, PycModule* mod, int at)
{
    int codeLen = code->code() != nullptr ? code->code()->length() : 0;
    if (at < 0 || at >= codeLen)
        return 0;
    int op = 0, arg = 0, next = at, end = at;
    for (int n = 0; n < 4; n++) {
        if (!ast_read_wordcode_instr(code->code(), mod, next, op, arg, next))
            break;
        end = next;
        if (op == Pyc::RETURN_VALUE || op == Pyc::RETURN_CONST_A || op == Pyc::RAISE_VARARGS_A
                || op == Pyc::RERAISE || op == Pyc::RERAISE_A
                || op == Pyc::JUMP_ABSOLUTE_A || op == Pyc::JUMP_FORWARD_A)
            return end - at;
    }
    return 0;
}

// 3.10 break inside try: after POP_BLOCK, an inlined finally, then a jump to the while
// exit or a byte-for-byte copy of that exit. Returns the offset just past that break.
static int ast_py310_while_break_end(PycRef<PycCode> code, PycModule* mod,
        std::stack<PycRef<ASTBlock> > blocks, const std::set<int>& skip, int afterPop)
{
    int whileEnd = 0;
    bool inTry = false;
    // Only blocks between the current point and the nearest while matter
    while (!blocks.empty()) {
        int kind = blocks.top()->blktype();
        if (kind == ASTBlock::BLK_WHILE) {
            whileEnd = blocks.top()->end();
            break;
        }
        if (kind == ASTBlock::BLK_FINALLY || kind == ASTBlock::BLK_EXCEPT
                || kind == ASTBlock::BLK_FOR || kind == ASTBlock::BLK_ASYNCFOR)
            return -1;
        if (kind == ASTBlock::BLK_TRY)
            inTry = true;
        blocks.pop();
    }
    int codeLen = code->code() != nullptr ? code->code()->length() : 0;
    if (!inTry || whileEnd <= afterPop || whileEnd > codeLen || code->code() == nullptr)
        return -1;
    int op = 0, arg = 0, next = afterPop, at = afterPop;
    while (at < codeLen && skip.count(at)
            && ast_read_wordcode_instr(code->code(), mod, at, op, arg, next))
        at = next;
    if (!ast_read_wordcode_instr(code->code(), mod, at, op, arg, next))
        return -1;
    int target = -1;
    if (op == Pyc::JUMP_ABSOLUTE_A)
        target = arg * (int)sizeof(uint16_t);
    else if (op == Pyc::JUMP_FORWARD_A)
        target = ast_relative_jump_target(mod, op, arg, next, false);
    if (target >= whileEnd)
        return next;
    int elen = whileEnd < codeLen ? ast_py310_exit_block_len(code, mod, whileEnd) : 0;
    if (elen > 0 && at + elen <= codeLen
            && memcmp(code->code()->value() + at, code->code()->value() + whileEnd, elen) == 0)
        return at + elen;
    return -1;
}

// 3.10 parses `else: return` before the except handler, so the else node is appended first
static void ast_py310_else_after_except(PycRef<ASTContainerBlock> cont)
{
    std::vector<PycRef<ASTNode> > order;
    while (cont->size() != 0) {
        order.push_back(cont->nodes().back());
        cont->removeLast();
    }
    bool hasExcept = false;
    for (int i = (int)order.size() - 1; i >= 0; --i) {
        PycRef<ASTNode> node = order[i];
        if (node != nullptr && node.type() == ASTNode::NODE_BLOCK
                && node.cast<ASTBlock>()->blktype() == ASTBlock::BLK_EXCEPT)
            hasExcept = true;
    }
    if (!hasExcept) {
        for (int i = (int)order.size() - 1; i >= 0; --i)
            cont->append(order[i]);
        return;
    }
    std::vector<PycRef<ASTNode> > before, elses, after;
    bool seenExcept = false;
    bool passedExcept = false;
    for (int i = (int)order.size() - 1; i >= 0; --i) {
        PycRef<ASTNode> node = order[i];
        bool isElse = node != nullptr && node.type() == ASTNode::NODE_BLOCK
                && node.cast<ASTBlock>()->blktype() == ASTBlock::BLK_ELSE;
        bool isExcept = node != nullptr && node.type() == ASTNode::NODE_BLOCK
                && node.cast<ASTBlock>()->blktype() == ASTBlock::BLK_EXCEPT;
        if (isElse && !passedExcept)
            elses.push_back(node);
        else {
            if (seenExcept && !isExcept)
                passedExcept = true;
            if (isExcept)
                seenExcept = true;
            if (passedExcept)
                after.push_back(node);
            else
                before.push_back(node);
        }
    }
    for (size_t i = 0; i < before.size(); i++)
        cont->append(before[i]);
    for (size_t i = 0; i < elses.size(); i++)
        cont->append(elses[i]);
    for (size_t i = 0; i < after.size(); i++)
        cont->append(after[i]);
}

static void ast_emit_copied_break(PycRef<ASTBlock>& curblock, PycBuffer& source, PycModule* mod,
        int& curpos, int& opcode, int& operand, int& pos, int breakEnd)
{
    curblock->append(new ASTKeyword(ASTKeyword::KW_BREAK));
    while (pos < breakEnd && !source.atEof()) {
        curpos = pos;
        bc_next(source, mod, opcode, operand, pos);
    }
}

// Pop the repeated test and close the BLK_WHILE opened at its entry guard
static bool ast_close_while_backedge(std::stack<PycRef<ASTBlock> >& blocks,
        PycRef<ASTBlock>& curblock, FastStack& stack,
        const std::map<int, int>& whileDupSkip, int& curpos,
        PycBuffer& source, PycModule* mod, int& opcode, int& operand, int& pos)
{
    bool hasWhile = false;
    {
        std::stack<PycRef<ASTBlock> > tmp = blocks;
        while (!tmp.empty()) {
            if (tmp.top()->blktype() == ASTBlock::BLK_WHILE) {
                hasWhile = true;
                break;
            }
            tmp.pop();
        }
    }
    if (!hasWhile)
        return false;
    if (!stack.empty())
        stack.pop();
    // Close blocks still open inside the loop body, then the BLK_WHILE itself
    while (blocks.size() > 1 && curblock->blktype() != ASTBlock::BLK_WHILE) {
        PycRef<ASTBlock> inner = curblock;
        blocks.pop();
        curblock = blocks.top();
        curblock->append(inner.cast<ASTNode>());
    }
    if (curblock->blktype() == ASTBlock::BLK_WHILE && blocks.size() > 1) {
        PycRef<ASTBlock> wh = curblock;
        blocks.pop();
        curblock = blocks.top();
        curblock->append(wh.cast<ASTNode>());
    }
    std::map<int, int>::const_iterator dup = whileDupSkip.find(curpos);
    while (dup != whileDupSkip.end() && pos < dup->second && !source.atEof()) {
        curpos = pos;
        bc_next(source, mod, opcode, operand, pos);
    }
    return true;
}

PycRef<ASTNode> BuildFromCode(PycRef<PycCode> code, PycModule* mod)
{
    const bool py313ClassBody = mod->verCompare(3, 13) >= 0
            && (code->flags() & PycCode::CO_NEWLOCALS) == 0
            && code->name()->strValue() != "<module>";
    cleanBuild = true;
    PycBuffer source(code->code()->value(), code->code()->length());
    const bool isModuleCode = code->name() != nullptr
            && code->name()->isEqual("<module>");

    FastStack stack((mod->majorVer() == 1) ? 20 : code->stackSize());
    stackhist_t stack_hist;

    std::stack<PycRef<ASTBlock> > blocks;
    PycRef<ASTBlock> defblock = new ASTBlock(ASTBlock::BLK_MAIN);
    defblock->init();
    PycRef<ASTBlock> curblock = defblock;
    blocks.push(defblock);

    int opcode, operand;
    int curpos = 0;
    int pos = 0;
    int unpack = 0;
    int unpackStar = -1;
    bool else_pop = false;
    bool need_try = false;
    bool variable_annotations = false;
    bool py39_except_bind_pending = false;
    bool py311_except_bind_pending = false;
    int py311_cleanup_sequences = 0;
    std::set<std::string> py311_except_bound_names;
    int py39_except_cleanup_var = -1;
    std::string py310SharedEpilogue;
    bool py310EpilogueEmitted = false;
    std::set<int> py310InlinedElseHandlers; // handler offset of a 3.10 `else: return`
    int py39_normal_cleanup_step = 0;
    int py39_handler_cleanup_step = 0;
    int py39_handler_cleanup_target = -1;
    std::vector<PycExceptionTableEntry> exception_entries;
    std::map<int, int> moduleImportTryEndByStart;
    std::map<int, int> tryReturnEndByStart;
    std::set<int> deferredTryEnds;
    size_t next_exception_entry = 0;

    /* Python 3.11 with-statement reconstruction state. */
    std::map<int, int> withBodyEndByBefore;   /* BEFORE_WITH pos -> body end */
    std::map<int, int> withResumeByBodyEnd;   /* body end -> resume offset */
    std::map<int, int> withReturnCleanupUntil; /* cleanup start -> RETURN_VALUE */
    std::map<int, int> withHandlerEndByStart;  /* WITH_EXCEPT_START -> cleanup end */
    int with_skip_until = 0;                   /* skip cleanup region < this */
    int with_return_cleanup_until = 0;         /* skip return __exit__ path < this */
    std::map<int, PycRef<ASTContainerBlock> > deferredExceptContainers;
    std::map<int, int> deferredHandlerLoopStart;
    // 3.12+ loops by FOR_ITER offset, and the one re-opened for code placed after an exception handler
    std::map<int, PycRef<ASTBlock> > forBlockAt;
    PycRef<ASTBlock> reopenedLoop;
    std::vector<PycRef<ASTContainerBlock> > activeDeferredExceptContainers;

    /* Python 3.11 try/finally reconstruction state. */
    std::map<int, int> finallyTryEndByStart;   /* entry start -> try body end */
    std::map<int, int> finallyEndByStart;      /* entry start -> finally end */
    std::map<int, int> finallyResumeByEnd;     /* finally end -> resume offset */
    std::map<int, int> finallyReturnByStart;   /* entry start -> return offset */
    std::set<int> finallyCopySkip;
    std::map<int, int> finallyHandlerByStart;
    std::map<int, PycRef<ASTBlock>> finallyReturnTryAt;
    std::map<int, int> finallyReturnSkipAt;    /* return offset -> handler cleanup end */
    std::map<int, PycRef<ASTNode>> finallyReturnValueAt;
    std::map<int, int> inlineCompSavedByStart;
    std::set<int> inlineCompSyntheticTargets;
    std::map<int, int> inlineCompSkipByTarget;
    std::set<int> inlineCompRestoreStores;
    bool inlineCompActive = false;
    int inlineCompLoopDepth = 0;
    int inlineCompMaxLoopDepth = 0;
    int inlineCompCleanupOps = 0;
    bool suppressNextPopTop = false;
    bool skipNextPopTop = false;
    // Chained comparison in progress: comparison so far and the copied middle operand; cleanup blocks to skip
    PycRef<ASTNode> chainLeft, chainMiddle;
    std::map<int, int> chainSkipAt;
    // Value short-circuit (`a or b`) operators pending at their jump target, innermost last
    std::map<int, std::vector<ASTBinary::BinOp> > py314ShortCircuitAt;

    /* Python 3.11 while-loop reconstruction state. */
    std::map<int, int> whileGuardEnd;          /* guard pos -> loop end */
    std::set<int> whileBackedges;              /* back-edge positions */
    std::set<int> whileLatchGuards;             /* repeated bottom tests */
    std::map<int, int> whileInvertedGuards;     // entry guard jumping into the body -> body start
    std::map<int, int> whileDupSkip;            // back-edge -> end of the duplicated exit block after it
    std::set<int> whileCondJumps;               // 3.10 header jumps that extend the while condition
    std::map<int, int> whileElseAt;             // 3.10 back-edge -> end of the else body
    std::set<int> whileAmbiguous;               // 3.10 while conditions the and/or folder cannot fold
    std::map<int, int> whileTrueAt;             // `while True:` head -> loop exit
    std::map<int, std::pair<PycRef<ASTBlock>, int> > elifElseEnd;  // elif end -> (elif, end of the else it replaced)

    /* Python 3.11 chained-comparison reconstruction state. */
    std::map<int, int> chainSkipJumps;         /* trailer JUMP_FORWARD -> body */
    std::map<int, int> trampolineExit;         /* trampoline POP_TOP -> exit */

    if (mod->verCompare(3, 11) >= 0) {
        exception_entries = code->exceptionTableEntries();
        for (const auto& entry : exception_entries) {
            if (entry.push_lasti || entry.end_offset <= entry.start_offset
                    || entry.end_offset >= entry.target)
                continue;
            int protectedEnd = entry.end_offset;
            for (const auto& continuation : exception_entries) {
                if (!continuation.push_lasti
                        && continuation.target == entry.target
                        && continuation.start_offset >= entry.start_offset
                        && continuation.end_offset < entry.target)
                    protectedEnd = std::max(protectedEnd,
                            continuation.end_offset);
            }
            int endOp = 0, endArg = 0, afterEnd = 0;
            auto isReturnOp = [](int op) {
                return op == Pyc::RETURN_VALUE
                    || op == Pyc::INSTRUMENTED_RETURN_VALUE_A
                    || op == Pyc::RETURN_CONST_A
                    || op == Pyc::INSTRUMENTED_RETURN_CONST_A;
            };
            bool readEnd = false;
            int endPos = protectedEnd;
            do {
                readEnd = ast_read_wordcode_instr(code->code(), mod,
                        endPos, endOp, endArg, afterEnd);
                endPos = afterEnd;
            } while (readEnd && endOp == Pyc::CACHE);
            bool endsWithReturn = readEnd && isReturnOp(endOp);
            if (!endsWithReturn && endOp == Pyc::POP_TOP) {
                /* Returning from inside a for loop first removes the hidden
                   iterator.  The cleanup and return cannot raise, so 3.13 can
                   place both just beyond the protected exception-table range:

                       POP_TOP
                       RETURN_CONST

                   Keep the return in the source try rather than attaching it
                   after the handler. */
                int returnOp = 0, returnArg = 0, afterReturn = 0;
                bool readReturn = false;
                int returnPos = afterEnd;
                // Nested loops and 3.15 pop more iterator slots; without RETURN_CONST (3.11, 3.14+) a constant load precedes the return
                bool loadedConst = false;
                do {
                    readReturn = ast_read_wordcode_instr(code->code(), mod,
                            returnPos, returnOp, returnArg, afterReturn);
                    returnPos = afterReturn;
                    bool constLoad = !loadedConst && (returnOp == Pyc::LOAD_CONST_A
                            || returnOp == Pyc::LOAD_SMALL_INT_A || returnOp == Pyc::LOAD_COMMON_CONSTANT_A);
                    if (constLoad)
                        loadedConst = true;
                    else if (returnOp == Pyc::POP_TOP && loadedConst)
                        break;
                    else if (returnOp != Pyc::CACHE && returnOp != Pyc::POP_TOP)
                        break;
                } while (readReturn);
                if (readReturn
                        && isReturnOp(returnOp) && afterReturn <= entry.target) {
                    endsWithReturn = true;
                    afterEnd = afterReturn;
                }
            }
            if (!endsWithReturn && endOp == Pyc::SWAP_A && (endArg == 2 || endArg == 3)) {
                /* RETURN_VALUE from a for loop uses SWAP 2; POP_TOP to retain
                   the return value while discarding the hidden iterator. */
                // Nested loops repeat the pair; 3.15 drops its two-slot iterator with SWAP 3 and two POP_TOPs
                int cleanupOp = 0, cleanupArg = 0, afterCleanup = 0, lastOp = endOp;
                int cleanupPos = afterEnd;
                bool readCleanup = false;
                while ((readCleanup = ast_read_wordcode_instr(code->code(), mod,
                                cleanupPos, cleanupOp, cleanupArg, afterCleanup))
                        && (cleanupOp == Pyc::CACHE || cleanupOp == Pyc::SWAP_A || cleanupOp == Pyc::POP_TOP)) {
                    if (cleanupOp != Pyc::CACHE)
                        lastOp = cleanupOp;
                    cleanupPos = afterCleanup;
                }
                if (readCleanup && lastOp == Pyc::POP_TOP && isReturnOp(cleanupOp)
                        && afterCleanup <= entry.target) {
                    endsWithReturn = true;
                    afterEnd = afterCleanup;
                }
            }
            if (!endsWithReturn
                    && (endOp == Pyc::JUMP_BACKWARD_A
                        || endOp == Pyc::JUMP_BACKWARD_NO_INTERRUPT_A
                        || endOp == Pyc::INSTRUMENTED_JUMP_BACKWARD_A)) {
                /* A top-tested while can end its protected range at the final
                   back-edge.  A following RETURN_CONST is still source text
                   inside the try, but CPython omits it from the exception table
                   because it cannot raise. */
                int returnOp = 0, returnArg = 0, afterReturn = 0;
                bool readReturn = false;
                int returnPos = afterEnd;
                do {
                    readReturn = ast_read_wordcode_instr(code->code(), mod,
                            returnPos, returnOp, returnArg, afterReturn);
                    returnPos = afterReturn;
                } while (readReturn && returnOp == Pyc::CACHE);
                if (readReturn
                        && isReturnOp(returnOp) && afterReturn <= entry.target) {
                    endsWithReturn = true;
                    afterEnd = afterReturn;
                }
            }
            if (endsWithReturn) {
                /* Exception tables stop before RETURN_VALUE because returning
                   cannot raise. A source try can also be split into several
                   protected ranges by earlier returns, so use the final range
                   sharing this handler rather than shortening the try at the
                   first return. */
                tryReturnEndByStart[entry.start_offset] = afterEnd;
            }
        }
        if (isModuleCode) {
            PycBuffer scan(code->code()->value(), code->code()->length());
            int scanOp = 0, scanOperand = 0, scanPos = 0;
            std::map<int, int> opAt;
            while (!scan.atEof()) {
                int current = scanPos;
                bc_next(scan, mod, scanOp, scanOperand, scanPos);
                opAt[current] = scanOp;
            }
            for (const auto& entry : exception_entries) {
                if (entry.push_lasti || entry.end_offset <= entry.start_offset
                        || entry.end_offset >= entry.target)
                    continue;
                bool imports = false;
                for (const auto& op : opAt) {
                    if (op.first >= entry.start_offset && op.first < entry.end_offset
                            && op.second == Pyc::IMPORT_NAME_A) {
                        imports = true;
                        break;
                    }
                }
                if (imports)
                    moduleImportTryEndByStart[entry.start_offset] = entry.end_offset;
            }
        }
        ScanWithBlocks(code, mod, exception_entries,
                       withBodyEndByBefore, withResumeByBodyEnd,
                       withReturnCleanupUntil, withHandlerEndByStart);
        ScanTryFinally(code, mod, exception_entries,
                        finallyTryEndByStart, finallyEndByStart, finallyResumeByEnd,
                        finallyReturnByStart, finallyCopySkip, finallyHandlerByStart);
        ScanInlineComprehensions(code, mod, exception_entries,
                inlineCompSavedByStart, inlineCompSyntheticTargets,
                inlineCompSkipByTarget, inlineCompRestoreStores);
        ScanWhileLoops(code, mod, whileGuardEnd, whileBackedges,
                       whileLatchGuards, whileInvertedGuards, whileDupSkip,
                       whileCondJumps, whileElseAt, whileAmbiguous);
        ScanInfiniteLoops(code, mod, exception_entries, whileBackedges, whileTrueAt);
        ScanChainedCompare(code, mod, chainSkipJumps, trampolineExit);
    } else if (mod->verCompare(3, 8) >= 0) {
        ScanWhileLoops(code, mod, whileGuardEnd, whileBackedges,
                       whileLatchGuards, whileInvertedGuards, whileDupSkip,
                       whileCondJumps, whileElseAt, whileAmbiguous);
        ScanInfiniteLoops(code, mod, exception_entries, whileBackedges, whileTrueAt);
    }

    std::set<int> exceptAsSkip, exceptAsBindStores, exceptSetups;
    std::map<int, int> forElseEnd;
    int forElse = 0;
    ScanExceptAsCleanup(code, mod, exceptAsSkip, exceptAsBindStores);
    ScanExceptSetups(code, mod, exceptAsSkip, exceptSetups);
    std::set<int> finallyHandlers;
    ScanFinallyExits(code, mod, exceptSetups, exceptAsSkip, finallyHandlers);
    std::map<int, int> builtinFastPathSkip;
    ScanBuiltinFastPaths(code, mod, builtinFastPathSkip);

    while (!source.atEof()) {
#if defined(BLOCK_DEBUG) || defined(STACK_DEBUG)
        fprintf(stderr, "%-7d", pos);
    #ifdef STACK_DEBUG
        fprintf(stderr, "%-5d", (unsigned int)stack_hist.size() + 1);
    #endif
    #ifdef BLOCK_DEBUG
        for (unsigned int i = 0; i < blocks.size(); i++)
            fprintf(stderr, "    ");
        fprintf(stderr, "%s (%d)", curblock->type_str(), curblock->end());
    #endif
        fprintf(stderr, "\n");
#endif

        /* Python 3.11 with-statement / try-finally: close the body at its end
           and enter the cleanup skip region BEFORE processing exception-table
           entries. An enclosing try re-protects the implicit __exit__/finally
           cleanup region, which would otherwise reopen a spurious try over it. */
        if (curblock->blktype() == ASTBlock::BLK_WITH
                && curblock->end() != 0
                && curblock->end() <= pos
                && blocks.size() > 1) {
            PycRef<ASTBlock> with = curblock;
            blocks.pop();
            curblock = blocks.top();
            curblock->append(with.cast<ASTNode>());
            auto rit = withResumeByBodyEnd.find(with->end());
            if (rit != withResumeByBodyEnd.end())
                with_skip_until = rit->second;
        }
        if (curblock->blktype() == ASTBlock::BLK_FINALLY
                && curblock->end() != 0
                && curblock->end() <= pos
                && blocks.size() > 1) {
            int finEnd = curblock->end();
            PycRef<ASTBlock> final = curblock;
            blocks.pop();
            curblock = blocks.top();
            curblock->append(final.cast<ASTNode>());
            if (curblock->blktype() == ASTBlock::BLK_CONTAINER && blocks.size() > 1) {
                PycRef<ASTBlock> cont = curblock;
                blocks.pop();
                curblock = blocks.top();
                curblock->append(cont.cast<ASTNode>());
            }
            auto rit = finallyResumeByEnd.find(finEnd);
            if (rit != finallyResumeByEnd.end())
                with_skip_until = rit->second;
        }
        if (with_skip_until > 0) {
            if (pos < with_skip_until) {
                curpos = pos;
                bc_next(source, mod, opcode, operand, pos);
                continue;
            }
            with_skip_until = 0;
        }
        auto fastPath = builtinFastPathSkip.find(pos);
        if (fastPath != builtinFastPathSkip.end()) {
            with_skip_until = fastPath->second;
            curpos = pos;
            bc_next(source, mod, opcode, operand, pos);
            continue;
        }
        if (exceptAsSkip.count(pos) || finallyCopySkip.count(pos)) {
            // 3.10 copies a while exit after POP_BLOCK and an inlined finally; that is still a break
            if (mod->verCompare(3, 10) == 0) {
                int breakOp = 0, breakArg = 0, afterPop = 0;
                if (ast_read_wordcode_instr(code->code(), mod, pos, breakOp, breakArg, afterPop)
                        && breakOp == Pyc::POP_BLOCK) {
                    int breakEnd = ast_py310_while_break_end(code, mod, blocks, exceptAsSkip, afterPop);
                    if (breakEnd > afterPop) {
                        ast_emit_copied_break(curblock, source, mod, curpos, opcode, operand, pos, breakEnd);
                        continue;
                    }
                }
            }
            curpos = pos;
            bc_next(source, mod, opcode, operand, pos);
            continue;
        }
        // 3.8-3.10 finally handler start: the try body ends here and the finally body begins
        if (finallyHandlers.count(pos)) {
            std::stack<PycRef<ASTBlock> > pending = blocks;
            while (!pending.empty() && (pending.top()->blktype() == ASTBlock::BLK_IF
                        || pending.top()->blktype() == ASTBlock::BLK_ELIF
                        || pending.top()->blktype() == ASTBlock::BLK_ELSE))
                pending.pop();
            if (!pending.empty() && pending.top()->blktype() == ASTBlock::BLK_TRY) {
                PycRef<ASTBlock> tryblk = pending.top();
                pending.pop();
                if (!pending.empty() && pending.top()->blktype() == ASTBlock::BLK_CONTAINER
                        && pending.top().cast<ASTContainerBlock>()->finally() == pos) {
                    while (curblock != tryblk && blocks.size() > 1) {
                        PycRef<ASTBlock> done = curblock;
                        blocks.pop();
                        curblock = blocks.top();
                        if (!(done->blktype() == ASTBlock::BLK_ELSE && done->nodes().empty()))
                            curblock->append(done.cast<ASTNode>());
                        if (!stack_hist.empty()) {
                            stack = stack_hist.top();
                            stack_hist.pop();
                        }
                    }
                    blocks.pop();
                    curblock = blocks.top();
                    curblock->append(tryblk.cast<ASTNode>());
                    if (!stack_hist.empty()) {
                        stack = stack_hist.top();
                        stack_hist.pop();
                    }
                    stack_hist.push(stack);
                    PycRef<ASTBlock> final = new ASTBlock(ASTBlock::BLK_FINALLY, 0, true);
                    blocks.push(final);
                    curblock = blocks.top();
                }
            }
        }
        auto inlineSkip = inlineCompSkipByTarget.find(pos);
        if (inlineSkip != inlineCompSkipByTarget.end()) {
            with_skip_until = inlineSkip->second;
            curpos = pos;
            bc_next(source, mod, opcode, operand, pos);
            continue;
        }
        if (with_return_cleanup_until > 0) {
            if (pos < with_return_cleanup_until) {
                curpos = pos;
                bc_next(source, mod, opcode, operand, pos);
                continue;
            }
            with_return_cleanup_until = 0;
        }
        auto return_cleanup = withReturnCleanupUntil.find(pos);
        if (return_cleanup != withReturnCleanupUntil.end()) {
            /* Keep the return value already on the evaluation stack and skip
               only the compiler-generated __exit__(None, None, None) path. */
            with_return_cleanup_until = return_cleanup->second;
            curpos = pos;
            bc_next(source, mod, opcode, operand, pos);
            continue;
        }
        auto with_handler = withHandlerEndByStart.find(pos);
        if (with_handler != withHandlerEndByStart.end()) {
            with_skip_until = with_handler->second;
            curpos = pos;
            bc_next(source, mod, opcode, operand, pos);
            continue;
        }
        auto chainSkip = chainSkipAt.find(pos);
        if (chainSkip != chainSkipAt.end()) {
            int to = chainSkip->second;
            chainSkipAt.erase(chainSkip);
            while (pos < to && !source.atEof()) {
                curpos = pos;
                bc_next(source, mod, opcode, operand, pos);
            }
            continue;
        }
        auto shortCircuit = py314ShortCircuitAt.find(pos);
        if (shortCircuit != py314ShortCircuitAt.end()) {
            for (auto op = shortCircuit->second.rbegin(); op != shortCircuit->second.rend(); ++op) {
                PycRef<ASTNode> right = stack.top();
                stack.pop();
                PycRef<ASTNode> left = stack.top();
                stack.pop();
                if (left != nullptr && right != nullptr)
                    stack.push(new ASTBinary(left, right, *op));
                else
                    stack.push(left != nullptr ? left : right);
            }
            py314ShortCircuitAt.erase(shortCircuit);
        }

        /* Python 3.14 may start a new protected range at the exact offset
           where an if-chain and its enclosing deferred try end. Close the
           completed source blocks before opening the new exception-table
           entry, otherwise the old try remains buried below the new one. */
        if (mod->verCompare(3, 14) >= 0 && else_pop) {
            while (blocks.size() > 1
                    && (curblock->blktype() == ASTBlock::BLK_IF
                            || curblock->blktype() == ASTBlock::BLK_ELIF
                            || curblock->blktype() == ASTBlock::BLK_ELSE)
                    && curblock->end() <= pos) {
                PycRef<ASTBlock> finished = curblock;
                if (!stack_hist.empty())
                    stack_hist.pop();
                blocks.pop();
                curblock = blocks.top();
                curblock->append(finished.cast<ASTNode>());
                CheckIfExpr(stack, curblock);
            }
            else_pop = false;
        }
        bool closedDeferredTryAtCurrentPos = false;
        if (mod->verCompare(3, 14) >= 0
                && curblock->blktype() == ASTBlock::BLK_TRY
                && curblock->end() == pos
                && deferredTryEnds.count(curblock->end())
                && blocks.size() > 2) {
            PycRef<ASTBlock> finished = curblock;
            blocks.pop();
            PycRef<ASTBlock> container = blocks.top();
            if (container->blktype() == ASTBlock::BLK_CONTAINER
                    && container.cast<ASTContainerBlock>()->hasExcept()) {
                blocks.pop();
                PycRef<ASTBlock> parent = blocks.top();
                container->append(finished.cast<ASTNode>());
                parent->append(container.cast<ASTNode>());
                deferredExceptContainers[
                        container.cast<ASTContainerBlock>()->except()] =
                        container.cast<ASTContainerBlock>();
                deferredTryEnds.erase(finished->end());
                curblock = parent;
                closedDeferredTryAtCurrentPos = true;
            } else {
                blocks.push(container);
                blocks.push(finished);
                curblock = finished;
            }
        }
        if (closedDeferredTryAtCurrentPos) {
            while (blocks.size() > 1
                    && (curblock->blktype() == ASTBlock::BLK_IF
                            || curblock->blktype() == ASTBlock::BLK_ELIF
                            || curblock->blktype() == ASTBlock::BLK_ELSE)
                    && curblock->end() <= pos) {
                PycRef<ASTBlock> finished = curblock;
                if (stack_hist.size() >= 2) {
                    FastStack deferredSnapshot = stack_hist.top();
                    stack_hist.pop();
                    stack_hist.pop();
                    stack_hist.push(deferredSnapshot);
                }
                blocks.pop();
                curblock = blocks.top();
                curblock->append(finished.cast<ASTNode>());
                CheckIfExpr(stack, curblock);
            }
        }
        if (mod->verCompare(3, 11) >= 0) {
            while (blocks.size() > 1
                    && (curblock->blktype() == ASTBlock::BLK_IF
                        || curblock->blktype() == ASTBlock::BLK_ELIF
                        || curblock->blktype() == ASTBlock::BLK_ELSE)
                    && curblock->end() <= pos) {
                PycRef<ASTBlock> finished = curblock;
                if (!stack_hist.empty()) {
                    if (curblock->end() == pos
                            && curblock->blktype() != ASTBlock::BLK_ELSE)
                        stack = stack_hist.top();
                    stack_hist.pop();
                }
                blocks.pop();
                curblock = blocks.top();
                curblock->append(finished.cast<ASTNode>());
                CheckIfExpr(stack, curblock);
                else_pop = false;
            }
        }
        if (mod->verCompare(3, 14) >= 0
                && curblock->blktype() == ASTBlock::BLK_WHILE
                && curblock->end() == pos && blocks.size() > 1) {
            PycRef<ASTBlock> finished = curblock;
            blocks.pop();
            curblock = blocks.top();
            curblock->append(finished.cast<ASTNode>());
        }
        /* Python 3.13 places an exception handler for a try nested in a loop
           after END_FOR.  Keep its completed container aside while linear
           decoding reaches the handler, then reattach it at PUSH_EXC_INFO. */
        /* A protected range may end before a non-raising return/cleanup, so
           linear decoding can reach the handler with its BLK_TRY still open.
           When the immediately enclosing container names this exact handler,
           close the try before decoding PUSH_EXC_INFO. */
        if (mod->verCompare(3, 11) >= 0
                && curblock->blktype() == ASTBlock::BLK_TRY
                && curblock->end() < pos && blocks.size() > 2) {
            std::stack<PycRef<ASTBlock> > pending = blocks;
            PycRef<ASTBlock> finished = pending.top();
            pending.pop();
            PycRef<ASTBlock> owner = pending.top();
            if (owner->blktype() == ASTBlock::BLK_CONTAINER
                    && owner.cast<ASTContainerBlock>()->except() == pos) {
                blocks.pop();
                curblock = blocks.top();
                curblock->append(finished.cast<ASTNode>());
                if (!stack_hist.empty()) {
                    stack = stack_hist.top();
                    stack_hist.pop();
                }
                deferredTryEnds.erase(finished->end());
            }
        }
        auto deferred = deferredExceptContainers.find(pos);
        if (deferred != deferredExceptContainers.end()) {
            /* Discard the protected-region snapshot. The following exception
               match creates the handler snapshot itself; unlike the normal
               path there is no provisional type-less except block here. */
            if (!stack_hist.empty()) {
                stack = stack_hist.top();
                stack_hist.pop();
            }
            blocks.push(deferred->second.cast<ASTBlock>());
            curblock = blocks.top();
            activeDeferredExceptContainers.push_back(deferred->second);
            deferredExceptContainers.erase(deferred);
        }

        while (next_exception_entry < exception_entries.size()
                && exception_entries[next_exception_entry].start_offset < pos) {
            next_exception_entry++;
        }
        while (next_exception_entry < exception_entries.size()
                && exception_entries[next_exception_entry].start_offset == pos
                && inlineCompSyntheticTargets.count(
                        exception_entries[next_exception_entry].target)) {
            next_exception_entry++;
        }
        while (next_exception_entry < exception_entries.size()) {
            const auto& cleanup = exception_entries[next_exception_entry];
            if (cleanup.start_offset != pos || cleanup.push_lasti)
                break;
            int cleanupOp = 0, cleanupArg = 0, cleanupNext = 0;
            if (!ast_read_wordcode_instr(code->code(), mod, cleanup.start_offset,
                                         cleanupOp, cleanupArg, cleanupNext))
                break;
            bool syntheticCleanup = cleanup.end_offset == cleanup.target
                    && cleanupOp == Pyc::POP_EXCEPT;
            if (mod->verCompare(3, 11) >= 0) {
                syntheticCleanup = cleanupOp == Pyc::POP_EXCEPT;
                if (cleanupOp == Pyc::COPY_A) {
                    int nextOp = 0, nextArg = 0, afterNext = 0;
                    syntheticCleanup = ast_read_wordcode_instr(code->code(), mod,
                            cleanupNext, nextOp, nextArg, afterNext)
                            && nextOp == Pyc::POP_EXCEPT;
                }
            }
            if (!syntheticCleanup)
                break;
            next_exception_entry++;
        }
        while (mod->verCompare(3, 14) >= 0
                && next_exception_entry < exception_entries.size()) {
            const auto& continuation = exception_entries[next_exception_entry];
            if (continuation.start_offset != pos || continuation.push_lasti
                    || !deferredExceptContainers.count(continuation.target))
                break;
            next_exception_entry++;
        }

        if (next_exception_entry < exception_entries.size()) {
            const auto& entry = exception_entries[next_exception_entry];
            if (entry.start_offset == pos
                    && !entry.push_lasti) {
                // SEND's StopIteration edge is not a source try
                int topOp = 0, topArg = 0, topNext = 0;
                bool awaitCleanup = code->code() != nullptr
                        && ast_read_wordcode_instr(code->code(), mod, entry.target, topOp, topArg, topNext)
                        && (topOp == Pyc::CLEANUP_THROW || topOp == Pyc::CALL_INTRINSIC_1_A
                            || topOp == Pyc::END_ASYNC_FOR || topOp == Pyc::END_ASYNC_FOR_A
                            || topOp == Pyc::INSTRUMENTED_END_ASYNC_FOR_A);
                if (awaitCleanup) {
                    next_exception_entry++;
                } else {
                auto fit = finallyTryEndByStart.find(entry.start_offset);
                bool finallyConsumed = false;
                if (fit != finallyTryEndByStart.end()) {
                    /* Python 3.11 try/finally: container carries the finally end
                       offset; the try body ends before the normal finally copy. */
                    int finEnd = finallyEndByStart[entry.start_offset];
                    PycRef<ASTBlock> cont = new ASTContainerBlock(finEnd, 0);
                    blocks.push(cont.cast<ASTBlock>());
                    curblock = blocks.top();

                    stack_hist.push(stack);
                    PycRef<ASTBlock> tryblock =
                            new ASTBlock(ASTBlock::BLK_TRY, fit->second, true);
                    blocks.push(tryblock.cast<ASTBlock>());
                    curblock = blocks.top();
                    auto ret = finallyReturnByStart.find(entry.start_offset);
                    if (ret != finallyReturnByStart.end()) {
                        finallyReturnTryAt[ret->second] = tryblock;
                        finallyReturnSkipAt[ret->second] = finallyResumeByEnd[finEnd];
                        finallyResumeByEnd[finEnd] = ret->second;
                    }
                    // An entry for an inner except handler also opens that try inside the finally's try
                    finallyConsumed = finallyHandlerByStart[entry.start_offset] == entry.target;
                    finallyTryEndByStart.erase(fit);
                    if (finallyConsumed)
                        next_exception_entry++;
                }
                if (!finallyConsumed) {
                    /* Python 3.11 splits a single try into several exception
                       table entries (all pointing at the same handler) when the
                       try body contains a nested try/except: the protected range
                       is broken around the inner handler. If a BLK_TRY with this
                       same handler target is already open, these later entries
                       are continuations of it, not new trys; skip them to avoid
                       a cascade of spurious nested trys. */
                    bool sameTryOpen = false;
                    {
                        std::stack<PycRef<ASTBlock> > tmp = blocks;
                        bool sawTry = false;
                        while (!tmp.empty()) {
                            PycRef<ASTBlock> b = tmp.top();
                            if (b->blktype() == ASTBlock::BLK_TRY
                                    && b->end() == entry.target) {
                                sameTryOpen = true;
                                break;
                            }
                            if (b->blktype() == ASTBlock::BLK_TRY)
                                sawTry = true;
                            else if (sawTry && b->blktype() == ASTBlock::BLK_CONTAINER
                                    && b.cast<ASTContainerBlock>()->except() == entry.target) {
                                sameTryOpen = true;
                                break;
                            }
                            tmp.pop();
                        }
                    }
                    if (sameTryOpen) {
                        next_exception_entry++;
                    } else {
                        if (curblock->blktype() == ASTBlock::BLK_CONTAINER) {
                            curblock.cast<ASTContainerBlock>()->setExcept(entry.target);
                        } else {
                            PycRef<ASTBlock> next = new ASTContainerBlock(0, entry.target);
                            blocks.push(next.cast<ASTBlock>());
                            curblock = blocks.top();
                        }

                        stack_hist.push(stack);
                        int tryEnd = entry.target;
                        if (mod->verCompare(3, 11) >= 0
                                && entry.end_offset > entry.start_offset
                                && entry.end_offset < entry.target) {
                            tryEnd = entry.end_offset;
                            int handlerBoundary = entry.target;
                            for (const auto& nested : exception_entries) {
                                if (nested.target > entry.end_offset
                                        && nested.target < handlerBoundary)
                                    handlerBoundary = nested.target;
                            }
                            for (const auto& later : exception_entries) {
                                if (!later.push_lasti && later.target == entry.target
                                        && later.start_offset >= entry.start_offset
                                        && later.start_offset < handlerBoundary
                                        && later.end_offset < entry.target)
                                    tryEnd = std::max(tryEnd, later.end_offset);
                            }
                        }
                        auto moduleImportEnd = moduleImportTryEndByStart.find(entry.start_offset);
                        if (moduleImportEnd != moduleImportTryEndByStart.end())
                            tryEnd = moduleImportEnd->second;
                        if (mod->verCompare(3, 11) >= 0
                                && entry.end_offset > entry.start_offset
                                && entry.end_offset < entry.target) {
                            int loopEnd = 0;
                            std::stack<PycRef<ASTBlock> > pending = blocks;
                            while (!pending.empty()) {
                                if (pending.top()->blktype() == ASTBlock::BLK_FOR
                                        || pending.top()->blktype() == ASTBlock::BLK_ASYNCFOR) {
                                    loopEnd = pending.top()->end();
                                    break;
                                }
                                pending.pop();
                            }
                            int lastProtectedEnd = entry.end_offset;
                            for (const auto& later : exception_entries) {
                                if (loopEnd != 0 && later.target == entry.target
                                        && later.start_offset >= entry.end_offset
                                        && later.start_offset < loopEnd) {
                                    lastProtectedEnd = std::max(lastProtectedEnd,
                                            later.end_offset);
                                }
                            }
                            if (loopEnd != 0)
                                tryEnd = lastProtectedEnd;
                        }
                        auto returnEnd = tryReturnEndByStart.find(entry.start_offset);
                        if (returnEnd != tryReturnEndByStart.end())
                            tryEnd = returnEnd->second;
                        PycRef<ASTBlock> tryblock = new ASTBlock(ASTBlock::BLK_TRY, tryEnd, true);
                        if (tryEnd != entry.target)
                            deferredTryEnds.insert(tryEnd);
                        blocks.push(tryblock.cast<ASTBlock>());
                        curblock = blocks.top();
                        next_exception_entry++;
                    }
                }
                }
            }
        }

        bool delayedTryReachedPastEnd = false;
        if (mod->verCompare(3, 11) >= 0
                && curblock->blktype() == ASTBlock::BLK_TRY
                && curblock->end() < pos && deferredTryEnds.count(curblock->end())
                && blocks.size() > 2) {
            if (mod->verCompare(3, 14) >= 0) {
                delayedTryReachedPastEnd = true;
            } else {
                std::stack<PycRef<ASTBlock> > pending = blocks;
                pending.pop();
                if (!pending.empty()
                        && pending.top()->blktype() == ASTBlock::BLK_CONTAINER) {
                    PycRef<ASTBlock> delayedContainer = pending.top();
                    pending.pop();
                    delayedTryReachedPastEnd = !pending.empty()
                            && (pending.top()->blktype() == ASTBlock::BLK_FOR
                                    || pending.top()->blktype() == ASTBlock::BLK_ASYNCFOR);
                    if (!delayedTryReachedPastEnd && !pending.empty()
                            && (pending.top()->blktype() == ASTBlock::BLK_IF
                                || pending.top()->blktype() == ASTBlock::BLK_ELIF
                                || pending.top()->blktype() == ASTBlock::BLK_ELSE)
                            && pending.top()->end() <= pos) {
                        /* A terminal return may close the innermost if one
                           instruction after the protected range. Defer its try
                           handler before the following failure branch is
                           decoded as an except body. */
                        delayedTryReachedPastEnd = true;
                    }
                    if (!delayedTryReachedPastEnd
                            && !activeDeferredExceptContainers.empty()
                            && delayedContainer
                                != activeDeferredExceptContainers.back().cast<ASTBlock>()) {
                        /* A handler deferred out of a loop may itself contain a
                           nested try/except. Its cleanup IF can keep that try
                           open past the protected end; defer the nested handler
                           as well and inherit the outer loop target. */
                        delayedTryReachedPastEnd = true;
                    }
                }
            }
        }
        if (curblock->blktype() == ASTBlock::BLK_TRY
                && (curblock->end() == pos || delayedTryReachedPastEnd)
                && blocks.size() > 1) {
            PycRef<ASTBlock> prev = curblock;
            blocks.pop();
            curblock = blocks.top();

            if (curblock->blktype() == ASTBlock::BLK_CONTAINER
                    && curblock.cast<ASTContainerBlock>()->hasExcept()) {
                PycRef<ASTContainerBlock> cont = curblock.cast<ASTContainerBlock>();

                if (mod->verCompare(3, 11) >= 0 && prev->end() < cont->except()
                        && deferredTryEnds.count(prev->end())) {
                    bool deferredContainer = false;
                    if (blocks.size() > 1) {
                        blocks.pop();
                        if (!blocks.empty()) {
                            cont->append(prev.cast<ASTNode>());
                            deferredExceptContainers[cont->except()] = cont;
                            curblock = blocks.top();
                            curblock->append(cont.cast<ASTNode>());
                            std::stack<PycRef<ASTBlock> > enclosing = blocks;
                            while (!enclosing.empty()) {
                                PycRef<ASTBlock> candidate = enclosing.top();
                                if (candidate->blktype() == ASTBlock::BLK_FOR
                                        || candidate->blktype() == ASTBlock::BLK_ASYNCFOR) {
                                    deferredHandlerLoopStart[cont->except()] =
                                            candidate.cast<ASTIterBlock>()->start();
                                    break;
                                }
                                enclosing.pop();
                            }
                            if (!deferredHandlerLoopStart.count(cont->except())
                                    && !activeDeferredExceptContainers.empty()) {
                                int outerHandler =
                                        activeDeferredExceptContainers.back()->except();
                                auto outerLoop = deferredHandlerLoopStart.find(outerHandler);
                                if (outerLoop != deferredHandlerLoopStart.end())
                                    deferredHandlerLoopStart[cont->except()] = outerLoop->second;
                            }
                            deferredTryEnds.erase(prev->end());
                            deferredContainer = true;
                        }
                        if (!deferredContainer)
                            blocks.push(cont.cast<ASTBlock>());
                    }
                    if (!deferredContainer) {
                        if (!stack_hist.empty()) {
                            stack = stack_hist.top();
                            stack_hist.pop();
                        }

                        for (const auto& node : prev->nodes()) {
                            curblock->append(node);
                        }

                        PycRef<ASTBlock> finished = curblock;
                        blocks.pop();
                        curblock = blocks.top();

                        for (const auto& node : finished->nodes()) {
                            curblock->append(node);
                        }

                        continue;
                    }
                }

                if (curblock->blktype() == ASTBlock::BLK_CONTAINER
                        && !blocks.empty() && blocks.top() == curblock) {
                    if (!stack_hist.empty()) {
                        stack = stack_hist.top();
                        stack_hist.pop();
                    }

                    curblock->append(prev.cast<ASTNode>());
                    stack_hist.push(stack);

                    PycRef<ASTBlock> except = new ASTCondBlock(ASTBlock::BLK_EXCEPT, 0, NULL, false);
                    except->init();
                    blocks.push(except);
                    curblock = blocks.top();
                }
            } else if (curblock->blktype() == ASTBlock::BLK_CONTAINER
                    && curblock.cast<ASTContainerBlock>()->hasFinally()) {
                /* Python 3.11 try/finally: the try body is followed by the
                    finally body (normal copy). */
                for (const auto& ret : finallyReturnTryAt) {
                    if (ret.second == prev && !stack.empty())
                        finallyReturnValueAt[ret.first] = stack.top();
                }
                if (!stack_hist.empty()) {
                    stack = stack_hist.top();
                    stack_hist.pop();
                }

                curblock->append(prev.cast<ASTNode>());

                int finEnd = curblock.cast<ASTContainerBlock>()->finally();
                PycRef<ASTBlock> final = new ASTBlock(ASTBlock::BLK_FINALLY, finEnd, true);
                final->init();
                blocks.push(final);
                curblock = blocks.top();
            } else {
                blocks.push(prev);
                curblock = prev;
            }
        }

        if (curblock->blktype() == ASTBlock::BLK_EXCEPT
                && curblock->end() == pos
                && blocks.size() > 1) {
            bool siblingExceptAhead = false;
            int matchOp = 0, matchArg = 0, matchNext = 0;
            if (ast_read_wordcode_instr(code->code(), mod, pos,
                        matchOp, matchArg, matchNext)
                    && (matchOp == Pyc::LOAD_GLOBAL_A
                        || matchOp == Pyc::LOAD_NAME_A
                        || matchOp == Pyc::LOAD_FAST_A)) {
                do {
                    if (!ast_read_wordcode_instr(code->code(), mod, matchNext,
                                matchOp, matchArg, matchNext))
                        break;
                } while (matchOp == Pyc::CACHE);
                siblingExceptAhead = matchOp == Pyc::CHECK_EXC_MATCH;
            }
            PycRef<ASTBlock> prev = curblock;
            blocks.pop();
            curblock = blocks.top();

            if (!stack_hist.empty()) {
                stack = stack_hist.top();
                stack_hist.pop();
            }

            if (prev->size() != 0 || !activeDeferredExceptContainers.empty()) {
                curblock->append(prev.cast<ASTNode>());
            }

            if (curblock->blktype() == ASTBlock::BLK_CONTAINER
                    && !curblock.cast<ASTContainerBlock>()->hasFinally()) {
                PycRef<ASTBlock> cont = curblock;
                if (!siblingExceptAhead) {
                    blocks.pop();
                    curblock = blocks.top();
                    if (!activeDeferredExceptContainers.empty()
                            && cont == activeDeferredExceptContainers.back().cast<ASTBlock>()) {
                        activeDeferredExceptContainers.pop_back();
                        // 3.12+ moves code after a try whose body always leaves the iteration behind the handler: re-open its loop
                        PycRef<ASTBlock> loop = mod->verCompare(3, 12) >= 0 && reopenedLoop == nullptr
                                ? ast_loop_of_handler_fragment(code, mod, exception_entries,
                                        cont.cast<ASTContainerBlock>()->except(), pos, forBlockAt)
                                : PycRef<ASTBlock>();
                        if (loop != nullptr) {
                            reopenedLoop = loop;
                            blocks.push(loop);
                            curblock = loop;
                            stack.push(loop.cast<ASTIterBlock>()->iter());
                        }
                    } else {
                        curblock->append(cont.cast<ASTNode>());
                    }
                }
            }

            /* Several source constructs can end at the same bytecode offset.
               Closing the except above may expose completed if-blocks and then
               the deferred try that owns them; finish that whole boundary now
               rather than waiting until the next handler has already started. */
            while (blocks.size() > 1
                    && (curblock->blktype() == ASTBlock::BLK_IF
                        || curblock->blktype() == ASTBlock::BLK_ELIF
                        || curblock->blktype() == ASTBlock::BLK_ELSE)
                    && curblock->end() <= pos) {
                PycRef<ASTBlock> finished = curblock;
                if (!stack_hist.empty())
                    stack_hist.pop();
                blocks.pop();
                curblock = blocks.top();
                curblock->append(finished.cast<ASTNode>());
                CheckIfExpr(stack, curblock);
            }
            if (curblock->blktype() == ASTBlock::BLK_TRY
                    && curblock->end() == pos
                    && deferredTryEnds.count(curblock->end())
                    && blocks.size() > 2) {
                PycRef<ASTBlock> finished = curblock;
                blocks.pop();
                PycRef<ASTBlock> container = blocks.top();
                if (container->blktype() == ASTBlock::BLK_CONTAINER
                        && container.cast<ASTContainerBlock>()->hasExcept()) {
                    blocks.pop();
                    PycRef<ASTBlock> parent = blocks.top();
                    container->append(finished.cast<ASTNode>());
                    parent->append(container.cast<ASTNode>());
                    int handler = container.cast<ASTContainerBlock>()->except();
                    deferredExceptContainers[handler] =
                            container.cast<ASTContainerBlock>();
                    deferredTryEnds.erase(finished->end());
                    curblock = parent;
                } else {
                    blocks.push(container);
                    blocks.push(finished);
                    curblock = finished;
                }
            }
        }

        // 3.11 loop whose last back-edge sits in an exception handler: nothing else closes it at its exit
        if (mod->verCompare(3, 11) == 0 && curblock->blktype() == ASTBlock::BLK_FOR
                && !curblock.cast<ASTIterBlock>()->isComprehension()
                && curblock->end() == pos && blocks.size() > 1) {
            PycRef<ASTBlock> loop = curblock;
            blocks.pop();
            curblock = blocks.top();
            curblock->append(loop.cast<ASTNode>());
        }

        // 3.12+ break out of a while loop: a copy of the loop's short returning exit block replaces the jump
        if (mod->verCompare(3, 12) >= 0) {
            PycRef<ASTBlock> loop;
            std::stack<PycRef<ASTBlock> > pending = blocks;
            while (!pending.empty() && loop == nullptr) {
                int bt = pending.top()->blktype();
                if (bt == ASTBlock::BLK_FOR || bt == ASTBlock::BLK_ASYNCFOR)
                    break;
                if (bt == ASTBlock::BLK_WHILE)
                    loop = pending.top();
                pending.pop();
            }
            int len = loop != nullptr && loop->end() > pos ? ast_returning_block_len(code, mod, loop->end()) : -1;
            if (len > 0 && pos + len <= loop->end()
                    && memcmp(code->code()->value() + pos, code->code()->value() + loop->end(), len) == 0) {
                ast_emit_for_break(blocks, curblock, stack, stack_hist, pos);
                int to = pos + len;
                while (pos < to && !source.atEof()) {
                    curpos = pos;
                    bc_next(source, mod, opcode, operand, pos);
                }
                continue;
            }
        }

        // An elif that ended before the else it replaced: the remaining code is its else branch
        auto elifElse = elifElseEnd.find(pos);
        if (elifElse != elifElseEnd.end()) {
            if (!curblock->nodes().empty() && curblock->nodes().back() == elifElse->second.first.cast<ASTNode>()
                    && elifElse->second.second > pos) {
                stack_hist.push(stack);
                PycRef<ASTBlock> elseblk = new ASTBlock(ASTBlock::BLK_ELSE, elifElse->second.second);
                elseblk->init();
                blocks.push(elseblk);
                curblock = elseblk;
            }
            elifElseEnd.erase(elifElse);
        }

        // `while True:` head: the loop opens before its first instruction
        auto whileTrue = whileTrueAt.find(pos);
        if (whileTrue != whileTrueAt.end()) {
            PycRef<ASTCondBlock> wh = new ASTCondBlock(ASTBlock::BLK_WHILE, whileTrue->second,
                                                       new ASTObject(Pyc_True), false);
            wh->init(ASTCondBlock::PRE_POPPED);
            blocks.push(wh.cast<ASTBlock>());
            curblock = blocks.top();
            whileTrueAt.erase(whileTrue);
        }

        curpos = pos;
        bc_next(source, mod, opcode, operand, pos);

        // 3.0-3.10 `except E as name`: the store of the caught exception binds the handler variable
        if (exceptAsBindStores.count(curpos)) {
            if (!stack.empty())
                stack.pop();
            PycRef<PycString> bound = opcode == Pyc::STORE_FAST_A ? code->getLocal(operand)
                    : opcode == Pyc::STORE_DEREF_A ? code->getCellVar(mod, operand)
                    : code->getName(operand);
            PycRef<ASTCondBlock> except = ast_find_except_bind_block(curblock, blocks);
            if (except != nullptr)
                except->setExceptVar(new ASTName(bound));
            else
                cleanBuild = false;
            continue;
        }
        if (py311_except_bind_pending
                && opcode != Pyc::CACHE
                && opcode != Pyc::NOT_TAKEN
                && opcode != Pyc::INSTRUMENTED_NOT_TAKEN_A
                && opcode != Pyc::STORE_FAST_A
                && opcode != Pyc::STORE_DEREF_A) {
            py311_except_bind_pending = false;
        }

        int cleanup_end = pos;
        if (mod->verCompare(3, 11) >= 0
                && ast_is_synthetic_exception_cleanup(code, mod, curpos,
                        cleanup_end)) {
            int loadOp = 0, loadArg = 0, afterLoad = 0;
            int storeOp = 0, storeArg = 0, afterStore = 0;
            if (ast_read_wordcode_instr(code->code(), mod, curpos, loadOp,
                        loadArg, afterLoad)
                    && ast_read_wordcode_instr(code->code(), mod, afterLoad,
                        storeOp, storeArg, afterStore)) {
                PycRef<PycString> cleanupName = storeOp == Pyc::STORE_FAST_A
                        ? code->getLocal(storeArg)
                        : code->getCellVar(mod, storeArg);
                if (cleanupName != nullptr
                        && py311_except_bound_names.count(
                            cleanupName->strValue())) {
                    while (pos < cleanup_end && !source.atEof())
                        bc_next(source, mod, opcode, operand, pos);
                    continue;
                }
            }
        }
        if (py311_cleanup_sequences > 0
                && curblock->blktype() == ASTBlock::BLK_EXCEPT
                && ast_is_synthetic_exception_cleanup(code, mod, curpos, cleanup_end)) {
            while (pos < cleanup_end && !source.atEof())
                bc_next(source, mod, opcode, operand, pos);
            py311_cleanup_sequences--;
            continue;
        }

        if (mod->verCompare(3, 9) >= 0 && mod->verCompare(3, 11) < 0
                && py39_except_cleanup_var >= 0) {
            bool is_none_const = false;
            if (opcode == Pyc::LOAD_CONST_A) {
                PycRef<PycObject> obj = code->getConst(operand);
                is_none_const = obj != nullptr && obj->type() == PycObject::TYPE_NONE;
            }

            if (py39_normal_cleanup_step == 1 && opcode == Pyc::LOAD_CONST_A && is_none_const) {
                py39_normal_cleanup_step = 2;
                continue;
            } else if (py39_normal_cleanup_step == 2
                       && (opcode == Pyc::STORE_FAST_A || opcode == Pyc::STORE_DEREF_A)
                       && operand == py39_except_cleanup_var) {
                py39_normal_cleanup_step = 3;
                continue;
            } else if (py39_normal_cleanup_step == 3
                       && (opcode == Pyc::DELETE_FAST_A || opcode == Pyc::DELETE_DEREF_A)
                       && operand == py39_except_cleanup_var) {
                py39_normal_cleanup_step = 0;
                continue;
            } else if (py39_normal_cleanup_step != 0) {
                py39_normal_cleanup_step = 0;
            }

            if (curpos == py39_handler_cleanup_target
                    && opcode == Pyc::LOAD_CONST_A && is_none_const) {
                py39_handler_cleanup_step = 2;
                continue;
            } else if (py39_handler_cleanup_step == 2
                       && (opcode == Pyc::STORE_FAST_A || opcode == Pyc::STORE_DEREF_A)
                       && operand == py39_except_cleanup_var) {
                py39_handler_cleanup_step = 3;
                continue;
            } else if (py39_handler_cleanup_step == 3
                       && (opcode == Pyc::DELETE_FAST_A || opcode == Pyc::DELETE_DEREF_A)
                       && operand == py39_except_cleanup_var) {
                py39_handler_cleanup_step = 4;
                continue;
            } else if (py39_handler_cleanup_step == 4
                       && (opcode == Pyc::RERAISE || opcode == Pyc::RERAISE_A)) {
                py39_handler_cleanup_step = 0;
                py39_handler_cleanup_target = -1;
                continue;
            } else if (py39_handler_cleanup_step != 0) {
                py39_handler_cleanup_step = 0;
            }
        }

        if (need_try && opcode != Pyc::SETUP_EXCEPT_A) {
            need_try = false;

            /* Store the current stack for the except/finally statement(s) */
            stack_hist.push(stack);
            PycRef<ASTBlock> tryblock = new ASTBlock(ASTBlock::BLK_TRY, curblock->end(), true);
            blocks.push(tryblock);
            curblock = blocks.top();
        } else if (else_pop
                && opcode != Pyc::JUMP_FORWARD_A
                && opcode != Pyc::JUMP_IF_FALSE_A
                && opcode != Pyc::JUMP_IF_FALSE_OR_POP_A
                && opcode != Pyc::POP_JUMP_IF_FALSE_A
                && opcode != Pyc::POP_JUMP_FORWARD_IF_FALSE_A
                && opcode != Pyc::JUMP_IF_TRUE_A
                && opcode != Pyc::JUMP_IF_TRUE_OR_POP_A
                && opcode != Pyc::POP_JUMP_IF_TRUE_A
                && opcode != Pyc::POP_JUMP_FORWARD_IF_TRUE_A
                && opcode != Pyc::POP_BLOCK) {
            else_pop = false;

            PycRef<ASTBlock> prev = curblock;
            while (prev->end() < pos
                    && prev->blktype() != ASTBlock::BLK_MAIN) {
                if (mod->verCompare(3, 11) >= 0
                        && prev->blktype() == ASTBlock::BLK_TRY
                        && blocks.size() > 2) {
                    blocks.pop();
                    PycRef<ASTBlock> container = blocks.top();
                    if (container->blktype() == ASTBlock::BLK_CONTAINER
                            && container.cast<ASTContainerBlock>()->hasExcept()
                            && prev->end() < container.cast<ASTContainerBlock>()->except()
                            && blocks.size() > 1) {
                        blocks.pop();
                        PycRef<ASTBlock> parent = blocks.top();
                        bool deferContainer = parent->blktype() == ASTBlock::BLK_FOR
                                || parent->blktype() == ASTBlock::BLK_ASYNCFOR;
                        if (mod->verCompare(3, 14) >= 0
                                && deferredTryEnds.count(prev->end()))
                            deferContainer = true;
                        if (deferContainer) {
                            container->append(prev.cast<ASTNode>());
                            parent->append(container.cast<ASTNode>());
                            deferredExceptContainers[
                                    container.cast<ASTContainerBlock>()->except()] =
                                    container.cast<ASTContainerBlock>();
                            deferredTryEnds.erase(prev->end());
                            curblock = parent;
                            prev = parent;
                            continue;
                        }
                        blocks.push(container);
                    }
                    blocks.push(prev);
                }
                if (prev->blktype() != ASTBlock::BLK_CONTAINER) {
                    if (prev->end() == 0) {
                        break;
                    }

                    /* We want to keep the stack the same, but we need to pop
                     * a level off the history. */
                    //stack = stack_hist.top();
                    if (!stack_hist.empty())
                        stack_hist.pop();
                }
                blocks.pop();

                if (blocks.empty())
                    break;

                curblock = blocks.top();
                curblock->append(prev.cast<ASTNode>());

                prev = curblock;

                CheckIfExpr(stack, curblock);
            }
        }

        switch (opcode) {
        case Pyc::BINARY_OP_A:
            {
                if (mod->verCompare(3, 14) >= 0 && operand == 26) {
                    PycRef<ASTNode> subscr = stack.top();
                    stack.pop();
                    PycRef<ASTNode> src = stack.top();
                    stack.pop();
                    stack.push(new ASTSubscr(src, subscr));
                    break;
                }
                ASTBinary::BinOp op = ASTBinary::from_binary_op(operand);
                if (op == ASTBinary::BIN_INVALID)
                    fprintf(stderr, "Unsupported `BINARY_OP` operand value: %d\n", operand);
                PycRef<ASTNode> right = stack.top();
                stack.pop();
                PycRef<ASTNode> left = stack.top();
                stack.pop();
                stack.push(new ASTBinary(left, right, op));
            }
            break;
        case Pyc::BINARY_ADD:
        case Pyc::BINARY_AND:
        case Pyc::BINARY_DIVIDE:
        case Pyc::BINARY_FLOOR_DIVIDE:
        case Pyc::BINARY_LSHIFT:
        case Pyc::BINARY_MODULO:
        case Pyc::BINARY_MULTIPLY:
        case Pyc::BINARY_OR:
        case Pyc::BINARY_POWER:
        case Pyc::BINARY_RSHIFT:
        case Pyc::BINARY_SUBTRACT:
        case Pyc::BINARY_TRUE_DIVIDE:
        case Pyc::BINARY_XOR:
        case Pyc::BINARY_MATRIX_MULTIPLY:
        case Pyc::INPLACE_ADD:
        case Pyc::INPLACE_AND:
        case Pyc::INPLACE_DIVIDE:
        case Pyc::INPLACE_FLOOR_DIVIDE:
        case Pyc::INPLACE_LSHIFT:
        case Pyc::INPLACE_MODULO:
        case Pyc::INPLACE_MULTIPLY:
        case Pyc::INPLACE_OR:
        case Pyc::INPLACE_POWER:
        case Pyc::INPLACE_RSHIFT:
        case Pyc::INPLACE_SUBTRACT:
        case Pyc::INPLACE_TRUE_DIVIDE:
        case Pyc::INPLACE_XOR:
        case Pyc::INPLACE_MATRIX_MULTIPLY:
            {
                ASTBinary::BinOp op = ASTBinary::from_opcode(opcode);
                if (op == ASTBinary::BIN_INVALID)
                    throw std::runtime_error("Unhandled opcode from ASTBinary::from_opcode");
                PycRef<ASTNode> right = stack.top();
                stack.pop();
                PycRef<ASTNode> left = stack.top();
                stack.pop();
                stack.push(new ASTBinary(left, right, op));
            }
            break;
        case Pyc::BINARY_SUBSCR:
            {
                PycRef<ASTNode> subscr = stack.top();
                stack.pop();
                PycRef<ASTNode> src = stack.top();
                stack.pop();
                stack.push(new ASTSubscr(src, subscr));
            }
            break;
        case Pyc::BREAK_LOOP:
            // Also ends ifs whose false branch jumps back to the loop head
            ast_emit_for_break(blocks, curblock, stack, stack_hist, curpos);
            break;
        case Pyc::BUILD_CLASS:
            {
                PycRef<ASTNode> class_code = stack.top();
                stack.pop();
                PycRef<ASTNode> bases = stack.top();
                stack.pop();
                PycRef<ASTNode> name = stack.top();
                stack.pop();
                stack.push(new ASTClass(class_code, bases, name));
            }
            break;
        case Pyc::BUILD_FUNCTION:
            {
                PycRef<ASTNode> fun_code = stack.top();
                stack.pop();
                stack.push(new ASTFunction(fun_code, {}, {}));
            }
            break;
        case Pyc::BUILD_LIST_A:
            {
                ASTList::value_t values;
                for (int i=0; i<operand; i++) {
                    values.push_front(stack.top());
                    stack.pop();
                }
                stack.push(new ASTList(values));
                if (inlineCompSavedByStart.count(curpos))
                    inlineCompActive = true;
            }
            break;
        case Pyc::BUILD_SET_A:
            {
                ASTSet::value_t values;
                for (int i=0; i<operand; i++) {
                    values.push_front(stack.top());
                    stack.pop();
                }
                stack.push(new ASTSet(values));
                if (inlineCompSavedByStart.count(curpos))
                    inlineCompActive = true;
            }
            break;
        case Pyc::BUILD_MAP_A:
            if (mod->verCompare(3, 5) >= 0) {
                auto map = new ASTMap;
                for (int i=0; i<operand; ++i) {
                    PycRef<ASTNode> value = stack.top();
                    stack.pop();
                    PycRef<ASTNode> key = stack.top();
                    stack.pop();
                    map->add(key, value);
                }
                stack.push(map);
                if (inlineCompSavedByStart.count(curpos))
                    inlineCompActive = true;
            } else {
                if (stack.top().type() == ASTNode::NODE_CHAINSTORE) {
                    stack.pop();
                }
                stack.push(new ASTMap());
            }
            break;
        case Pyc::BUILD_CONST_KEY_MAP_A:
            // Top of stack will be a tuple of keys.
            // Values will start at TOS - 1.
            {
                PycRef<ASTNode> keys = stack.top();
                stack.pop();

                ASTConstMap::values_t values;
                values.reserve(operand);
                for (int i = 0; i < operand; ++i) {
                    PycRef<ASTNode> value = stack.top();
                    stack.pop();
                    values.push_back(value);
                }

                stack.push(new ASTConstMap(keys, values));
            }
            break;
        case Pyc::STORE_MAP:
            {
                PycRef<ASTNode> key = stack.top();
                stack.pop();
                PycRef<ASTNode> value = stack.top();
                stack.pop();
                PycRef<ASTMap> map = stack.top().cast<ASTMap>();
                map->add(key, value);
            }
            break;
        case Pyc::MAP_ADD_A:
            {
                PycRef<ASTNode> value = stack.top();
                stack.pop();
                PycRef<ASTNode> key = stack.top();
                stack.pop();
                // Before 3.8 MAP_ADD has the key at TOS and the value below it
                if (mod->verCompare(3, 8) < 0)
                    std::swap(key, value);
                if (curblock->blktype() == ASTBlock::BLK_FOR
                        && curblock.cast<ASTIterBlock>()->isComprehension()) {
                    ASTMap* result = new ASTMap;
                    result->add(key, value);
                    if (!stack.empty())
                        stack.pop();
                    stack.push(new ASTComprehension(result));
                    break;
                }
                PycRef<ASTNode> target = stack.top(operand);

                if (target != nullptr && target.type() == ASTNode::NODE_MAP) {
                    target.cast<ASTMap>()->add(key, value);
                } else if (curblock != nullptr) {
                    cleanBuild = false;
                    curblock->append(new ASTUnsupported("# unsupported MAP_ADD target"));
                }
            }
            break;
        case Pyc::DICT_UPDATE_A:
        case Pyc::DICT_MERGE_A:
            {
                PycRef<ASTNode> rhs = stack.top();
                stack.pop();
                PycRef<ASTNode> target = stack.top(operand);

                // Call-site **kwargs merge into the map at TOS; rebuild it so const-key maps and dynamic parts combine
                if (operand == 1 && rhs != nullptr && (target.type() == ASTNode::NODE_MAP
                            || target.type() == ASTNode::NODE_CONST_MAP)) {
                    stack.pop();
                    PycRef<ASTMap> merged = new ASTMap();
                    ast_merge_mapping(merged, target);
                    ast_merge_mapping(merged, rhs);
                    stack.push(merged.cast<ASTNode>());
                } else if (target != nullptr && target.type() == ASTNode::NODE_MAP
                        && rhs != nullptr && rhs.type() == ASTNode::NODE_MAP) {
                    for (const auto& val : rhs.cast<ASTMap>()->values()) {
                        target.cast<ASTMap>()->add(val.first, val.second);
                    }
                } else if (target != nullptr && target.type() == ASTNode::NODE_MAP
                        && rhs != nullptr) {
                    /* Preserve a dynamic dictionary update as {**expr}. */
                    target.cast<ASTMap>()->add(nullptr, rhs);
                } else if (curblock != nullptr) {
                    cleanBuild = false;
                    curblock->append(new ASTUnsupported("# unsupported DICT_UPDATE/DICT_MERGE"));
                }
            }
            break;
        case Pyc::BUILD_SLICE_A:
            {
                if (operand == 2) {
                    PycRef<ASTNode> end = stack.top();
                    stack.pop();
                    PycRef<ASTNode> start = stack.top();
                    stack.pop();

                    if (start.type() == ASTNode::NODE_OBJECT
                            && start.cast<ASTObject>()->object() == Pyc_None) {
                        start = NULL;
                    }

                    if (end.type() == ASTNode::NODE_OBJECT
                            && end.cast<ASTObject>()->object() == Pyc_None) {
                        end = NULL;
                    }

                    if (start == NULL && end == NULL) {
                        stack.push(new ASTSlice(ASTSlice::SLICE0));
                    } else if (start == NULL) {
                        stack.push(new ASTSlice(ASTSlice::SLICE2, start, end));
                    } else if (end == NULL) {
                        stack.push(new ASTSlice(ASTSlice::SLICE1, start, end));
                    } else {
                        stack.push(new ASTSlice(ASTSlice::SLICE3, start, end));
                    }
                } else if (operand == 3) {
                    PycRef<ASTNode> step = stack.top();
                    stack.pop();
                    PycRef<ASTNode> end = stack.top();
                    stack.pop();
                    PycRef<ASTNode> start = stack.top();
                    stack.pop();

                    if (start.type() == ASTNode::NODE_OBJECT
                            && start.cast<ASTObject>()->object() == Pyc_None) {
                        start = NULL;
                    }

                    if (end.type() == ASTNode::NODE_OBJECT
                            && end.cast<ASTObject>()->object() == Pyc_None) {
                        end = NULL;
                    }

                    if (step.type() == ASTNode::NODE_OBJECT
                            && step.cast<ASTObject>()->object() == Pyc_None) {
                        step = NULL;
                    }

                    /* We have to do this as a slice where one side is another slice */
                    /* [[a:b]:c] */

                    if (start == NULL && end == NULL) {
                        stack.push(new ASTSlice(ASTSlice::SLICE0));
                    } else if (start == NULL) {
                        stack.push(new ASTSlice(ASTSlice::SLICE2, start, end));
                    } else if (end == NULL) {
                        stack.push(new ASTSlice(ASTSlice::SLICE1, start, end));
                    } else {
                        stack.push(new ASTSlice(ASTSlice::SLICE3, start, end));
                    }

                    PycRef<ASTNode> lhs = stack.top();
                    stack.pop();

                    if (step == NULL) {
                        stack.push(new ASTSlice(ASTSlice::SLICE1, lhs, step));
                    } else {
                        stack.push(new ASTSlice(ASTSlice::SLICE3, lhs, step));
                    }
                }
            }
            break;
        case Pyc::BUILD_STRING_A:
            {
                // Nearly identical logic to BUILD_LIST
                ASTList::value_t values;
                for (int i = 0; i < operand; i++) {
                    values.push_front(stack.top());
                    stack.pop();
                }
                stack.push(new ASTJoinedStr(values));
            }
            break;
        case Pyc::BUILD_TUPLE_A:
            {
                // if class is a closure code, ignore this tuple
                PycRef<ASTNode> tos = stack.top();
                if (tos && tos->type() == ASTNode::NODE_LOADBUILDCLASS) {
                    break;
                }

                ASTTuple::value_t values;
                values.resize(operand);
                for (int i=0; i<operand; i++) {
                    values[operand-i-1] = stack.top();
                    stack.pop();
                }
                stack.push(new ASTTuple(values));
            }
            break;
        case Pyc::KW_NAMES_A:
            {

                int kwparams = code->getConst(operand).cast<PycTuple>()->size();
                ASTKwNamesMap kwparamList;
                std::vector<PycRef<PycObject>> keys = code->getConst(operand).cast<PycSimpleSequence>()->values();
                for (int i = 0; i < kwparams; i++) {
                    kwparamList.add(new ASTObject(keys[kwparams - i - 1]), stack.top());
                    stack.pop();
                }
                stack.push(new ASTKwNamesMap(kwparamList));
            }
            break;
        case Pyc::CALL_A:
        case Pyc::CALL_FUNCTION_A:
        case Pyc::INSTRUMENTED_CALL_A:
        case Pyc::CALL_KW_A:
        case Pyc::INSTRUMENTED_CALL_KW_A:
            {
                int kwparams = (operand & 0xFF00) >> 8;
                int pparams = (operand & 0xFF);
                ASTCall::kwparam_t kwparamList;
                ASTCall::pparam_t pparamList;

                // Detect __build_class__ calls on a stack copy so the generic call path sees the original
                {
                    FastStack trial = stack;
                    ASTCall::kwparam_t classKwargs;
                    int npos = -1;
                    if (opcode == Pyc::CALL_KW_A || opcode == Pyc::INSTRUMENTED_CALL_KW_A) {
                        PycRef<PycSimpleSequence> keySeq = ast_kw_names_tuple(trial.top());
                        if (keySeq != nullptr) {
                            trial.pop();
                            const auto& keyValues = keySeq->values();
                            for (int i = (int)keyValues.size() - 1; i >= 0; --i) {
                                classKwargs.push_front(std::make_pair(
                                        new ASTObject(keyValues[i]), trial.top()));
                                trial.pop();
                            }
                            npos = operand - (int)keyValues.size();
                        }
                    } else if (mod->verCompare(3, 11) >= 0) {
                        // 3.11/3.12 class keywords (metaclass=) come from a KW_NAMES map stored last-key-first
                        npos = operand;
                        if (trial.top().type() == ASTNode::NODE_KW_NAMES_MAP) {
                            PycRef<ASTKwNamesMap> km = trial.top().cast<ASTKwNamesMap>();
                            trial.pop();
                            for (const auto& kv : km->values()) {
                                classKwargs.push_front(kv);
                                --npos;
                            }
                        }
                    } else if (mod->verCompare(3, 6) < 0) {
                        for (int i = 0; i < kwparams; i++) {
                            PycRef<ASTNode> val = trial.top();
                            trial.pop();
                            PycRef<ASTNode> key = trial.top();
                            trial.pop();
                            classKwargs.push_front(std::make_pair(key, val));
                        }
                        npos = pparams;
                    } else {
                        npos = operand;
                    }
                    if (ast_try_build_class(trial, mod, npos, classKwargs)) {
                        stack = trial;
                        break;
                    }
                }

                /*
                KW_NAMES(i)
                    Stores a reference to co_consts[consti] into an internal variable for use by CALL.
                    co_consts[consti] must be a tuple of strings.
                    New in version 3.11.
                */
                if (opcode == Pyc::CALL_KW_A || opcode == Pyc::INSTRUMENTED_CALL_KW_A) {
                    PycRef<ASTNode> keys_node = stack.top();
                    stack.pop();
                    if (keys_node != nullptr && keys_node.type() == ASTNode::NODE_OBJECT
                            && keys_node.cast<ASTObject>()->object() != nullptr
                            && (keys_node.cast<ASTObject>()->object().type() == PycObject::TYPE_TUPLE
                                || keys_node.cast<ASTObject>()->object().type() == PycObject::TYPE_SMALL_TUPLE)) {
                        PycTuple::value_t key_values = keys_node.cast<ASTObject>()->object().cast<PycSimpleSequence>()->values();
                        kwparams = (int)key_values.size();
                        pparams = operand - kwparams;
                        for (int i = 0; i < kwparams; i++) {
                            PycRef<ASTNode> val = stack.top();
                            stack.pop();
                            kwparamList.push_front(std::make_pair(new ASTObject(key_values[kwparams - i - 1]), val));
                        }
                    } else {
                        cleanBuild = false;
                        pparams = operand;
                    }
                } else if (mod->verCompare(3, 11) >= 0) {
                    PycRef<ASTNode> object_or_map = stack.top();
                    if (object_or_map.type() == ASTNode::NODE_KW_NAMES_MAP) {
                        stack.pop();
                        PycRef<ASTKwNamesMap> kwparams_map = object_or_map.cast<ASTKwNamesMap>();
                        for (ASTKwNamesMap::map_t::const_iterator it = kwparams_map->values().begin(); it != kwparams_map->values().end(); it++) {
                            kwparamList.push_front(std::make_pair(it->first, it->second));
                            pparams -= 1;
                        }
                    }
                }
                else {
                    for (int i = 0; i < kwparams; i++) {
                        PycRef<ASTNode> val = stack.top();
                        stack.pop();
                        PycRef<ASTNode> key = stack.top();
                        stack.pop();
                        kwparamList.push_front(std::make_pair(key, val));
                    }
                }
                for (int i=0; i<pparams; i++) {
                    PycRef<ASTNode> param = stack.top();
                    stack.pop();
                    pparamList.push_front(ast_decorated_definition_name(curblock, param));
                }
                PycRef<ASTNode> func = stack.top();
                stack.pop();

                // Pre-3.11 comprehensions are separate code objects called with the iterable
                if (mod->verCompare(3, 11) < 0 && pparamList.size() == 1 && kwparamList.empty()) {
                    PycRef<ASTNode> inlined = ast_inline_comprehension(func, pparamList.front(), mod);
                    if (inlined != nullptr) {
                        stack.push(inlined);
                        break;
                    }
                }

                bool isDecoratorApply = false;
                bool compInlined = false;
                bool newerCompCall = false;
                if (mod->verCompare(3, 12) >= 0 && mod->verCompare(3, 14) < 0
                        && !stack.empty() && stack.top() != nullptr
                        && stack.top().type() == ASTNode::NODE_FUNCTION) {
                    PycRef<PycCode> possibleComp = stack.top().cast<ASTFunction>()->code()
                            .cast<ASTObject>()->object().cast<PycCode>();
                    const char* possibleName = possibleComp->name()->value();
                    newerCompCall = possibleName
                            && (!strcmp(possibleName, "<listcomp>")
                                || !strcmp(possibleName, "<setcomp>")
                                || !strcmp(possibleName, "<dictcomp>")
                                || !strcmp(possibleName, "<genexpr>"));
                }
                if ((opcode == Pyc::CALL_A || opcode == Pyc::INSTRUMENTED_CALL_A)
                        && mod->verCompare(3, 11) >= 0
                        && (mod->verCompare(3, 12) < 0 || newerCompCall)) {
                    if (!stack.empty() && stack.top() == nullptr) {
                        /* Normal call: discard the NULL self slot. */
                        stack.pop();
                    } else if (!stack.empty() && stack.top() != nullptr) {
                        /* Python 3.11 leaves a non-NULL value in the self slot
                           (no PUSH_NULL) in two cases we reconstruct here:
                            - decorator application: TOS is the decorated
                              function/class, the real callable is below it;
                            - comprehension/genexpr call: the callable below is a
                              comprehension code object and TOS is the iterable. */
                        PycRef<ASTNode> below = stack.top();

                        bool topIsDecoTarget = ast_is_decorator_target(func);

                        bool belowIsComp = false;
                        if (below != NULL && below.type() == ASTNode::NODE_FUNCTION) {
                            PycRef<PycCode> bcode = below.cast<ASTFunction>()->code()
                                    .cast<ASTObject>()->object().cast<PycCode>();
                            const char* bnm = bcode->name()->value();
                            belowIsComp = bnm && (!strcmp(bnm, "<listcomp>")
                                    || !strcmp(bnm, "<setcomp>")
                                    || !strcmp(bnm, "<dictcomp>")
                                    || !strcmp(bnm, "<genexpr>"));
                        }

                        if (belowIsComp) {
                            /* Inline the comprehension. The callable is `below`
                               and the iterable is `func` (TOS). Decompile the
                               comprehension body and substitute its implicit
                               ".0" iterator with the real iterable. */
                            PycRef<ASTNode> comp = ast_inline_comprehension(below, func, mod);
                            if (comp != NULL) {
                                stack.pop();   /* remove the comprehension callable */
                                stack.push(comp);
                                compInlined = true;
                            }
                            /* else: leave as-is and fall through to a plain call. */
                        } else if (topIsDecoTarget) {
                            /* Decorator application: `func` (TOS) is the decorated
                               target, the real callable is below. */
                            PycRef<ASTNode> target = ast_decorated_definition_name(curblock, func);
                            func = stack.top();
                            stack.pop();
                            pparamList.push_front(target);
                            isDecoratorApply = true;
                        }
                        /* else: a non-null self slot we don't special-case (e.g.
                           method calls collapsed by LOAD_METHOD); behave as before
                           with `func` as the callable. */
                    }
                } else if (opcode == Pyc::CALL_A || opcode == Pyc::INSTRUMENTED_CALL_A
                        || opcode == Pyc::CALL_KW_A || opcode == Pyc::INSTRUMENTED_CALL_KW_A) {
                    PycRef<ASTNode> inlinedComp;
                    if (func != nullptr && !stack.empty() && stack.top() != nullptr
                            && pparamList.empty() && kwparamList.empty())
                        inlinedComp = ast_inline_comprehension(stack.top(), func, mod);
                    if (inlinedComp != nullptr) {
                        // 3.14+ generator expression call: [genexpr function, iterator] in the call slots
                        stack.pop();
                        stack.push(inlinedComp);
                        compInlined = true;
                    } else if (func != nullptr && !stack.empty() && stack.top() != nullptr
                            && ast_is_decorator_target(func)) {
                        // 3.12+ both call slots non-NULL means deco(target), i.e. a decorator application
                        PycRef<ASTNode> target = ast_decorated_definition_name(curblock, func);
                        func = stack.top();
                        stack.pop();
                        pparamList.push_front(target);
                        isDecoratorApply = true;
                    } else {
                        // 3.12+ call-slot conventions: drop the NULL self slot
                        ast_consume_call_self_slot(stack, func);
                    }
                }

                if (!compInlined) {
                    PycRef<ASTNode> callNode = new ASTCall(func, pparamList, kwparamList);
                    if (isDecoratorApply)
                        callNode.cast<ASTCall>()->setDecorator(true);
                    stack.push(callNode);
                }
            }
            break;
        case Pyc::CALL_FUNCTION_VAR_A:
            {
                PycRef<ASTNode> var = stack.top();
                stack.pop();
                int kwparams = (operand & 0xFF00) >> 8;
                int pparams = (operand & 0xFF);
                ASTCall::kwparam_t kwparamList;
                ASTCall::pparam_t pparamList;
                for (int i=0; i<kwparams; i++) {
                    PycRef<ASTNode> val = stack.top();
                    stack.pop();
                    PycRef<ASTNode> key = stack.top();
                    stack.pop();
                    kwparamList.push_front(std::make_pair(key, val));
                }
                for (int i=0; i<pparams; i++) {
                    pparamList.push_front(stack.top());
                    stack.pop();
                }
                PycRef<ASTNode> func = stack.top();
                stack.pop();

                PycRef<ASTNode> call = new ASTCall(func, pparamList, kwparamList);
                call.cast<ASTCall>()->setVar(var);
                stack.push(call);
            }
            break;
        case Pyc::CALL_FUNCTION_KW_A:
            if (mod->verCompare(3, 6) >= 0) {
                // 3.6+ CALL_FUNCTION_KW: TOS is the keyword-name tuple, values are the last args
                PycRef<PycSimpleSequence> keySeq = ast_kw_names_tuple(stack.top());
                if (keySeq != nullptr) {
                    stack.pop();
                    const auto& keyValues = keySeq->values();
                    ASTCall::kwparam_t kwparamList;
                    for (int i = (int)keyValues.size() - 1; i >= 0; --i) {
                        kwparamList.push_front(std::make_pair(
                                new ASTObject(keyValues[i]), stack.top()));
                        stack.pop();
                    }
                    int pparams = operand - (int)keyValues.size();
                    if (ast_try_build_class(stack, mod, pparams, kwparamList))
                        break;

                    ASTCall::pparam_t pparamList;
                    for (int i = 0; i < pparams; i++) {
                        pparamList.push_front(stack.top());
                        stack.pop();
                    }
                    PycRef<ASTNode> func = stack.top();
                    stack.pop();
                    stack.push(new ASTCall(func, pparamList, kwparamList));
                    break;
                }
            }
            {
                PycRef<ASTNode> kw = stack.top();
                stack.pop();
                int kwparams = (operand & 0xFF00) >> 8;
                int pparams = (operand & 0xFF);
                ASTCall::kwparam_t kwparamList;
                ASTCall::pparam_t pparamList;
                for (int i=0; i<kwparams; i++) {
                    PycRef<ASTNode> val = stack.top();
                    stack.pop();
                    PycRef<ASTNode> key = stack.top();
                    stack.pop();
                    kwparamList.push_front(std::make_pair(key, val));
                }
                for (int i=0; i<pparams; i++) {
                    pparamList.push_front(stack.top());
                    stack.pop();
                }
                PycRef<ASTNode> func = stack.top();
                stack.pop();

                PycRef<ASTNode> call = new ASTCall(func, pparamList, kwparamList);
                call.cast<ASTCall>()->setKW(kw);
                stack.push(call);
            }
            break;
        case Pyc::CALL_FUNCTION_VAR_KW_A:
            {
                PycRef<ASTNode> kw = stack.top();
                stack.pop();
                PycRef<ASTNode> var = stack.top();
                stack.pop();
                int kwparams = (operand & 0xFF00) >> 8;
                int pparams = (operand & 0xFF);
                ASTCall::kwparam_t kwparamList;
                ASTCall::pparam_t pparamList;
                for (int i=0; i<kwparams; i++) {
                    PycRef<ASTNode> val = stack.top();
                    stack.pop();
                    PycRef<ASTNode> key = stack.top();
                    stack.pop();
                    kwparamList.push_front(std::make_pair(key, val));
                }
                for (int i=0; i<pparams; i++) {
                    pparamList.push_front(stack.top());
                    stack.pop();
                }
                PycRef<ASTNode> func = stack.top();
                stack.pop();

                PycRef<ASTNode> call = new ASTCall(func, pparamList, kwparamList);
                call.cast<ASTCall>()->setKW(kw);
                call.cast<ASTCall>()->setVar(var);
                stack.push(call);
            }
            break;
        case Pyc::CALL_FUNCTION_EX_A:
        case Pyc::INSTRUMENTED_CALL_FUNCTION_EX_A:
            {
                /* Call with iterable args and (optionally) a mapping of kwargs.
                   Low bit of the flag operand means a kwargs mapping is present. */
                PycRef<ASTNode> kw;
                // 3.14+ always has a kwargs slot (NULL when absent); older versions flag it in bit 0
                if (mod->verCompare(3, 14) >= 0 || (operand & 0x01)) {
                    kw = stack.top();
                    stack.pop();
                }
                PycRef<ASTNode> var = stack.top();
                stack.pop();
                PycRef<ASTNode> func = stack.top();
                stack.pop();
                /* In 3.11-3.13 PUSH_NULL may leave the null call slot either
                   immediately above or below the callable. */
                if (mod->verCompare(3, 11) >= 0)
                    ast_consume_call_self_slot(stack, func);

                // Spread the built *args sequence and **kwargs mapping into ordinary call parameters
                std::vector<PycRef<ASTNode> > args;
                if (var.type() == ASTNode::NODE_TUPLE || var.type() == ASTNode::NODE_LIST
                        || var.type() == ASTNode::NODE_OBJECT)
                    ast_append_unpacked(args, var);
                else
                    args.push_back(new ASTUnary(var, ASTUnary::UN_STAR));
                ASTCall::kwparam_t kwargs;
                if (kw != NULL) {
                    PycRef<ASTMap> kwmap = new ASTMap();
                    ast_merge_mapping(kwmap, kw);
                    for (const auto& kv : kwmap->values()) {
                        bool isName = kv.first == nullptr
                                || (kv.first.type() == ASTNode::NODE_OBJECT
                                    && kv.first.cast<ASTObject>()->object().try_cast<PycString>() != nullptr);
                        if (isName) {
                            kwargs.push_back(kv);
                        } else {
                            // Non-identifier key: keep it inside a **{...} mapping
                            PycRef<ASTMap> rest = new ASTMap();
                            rest->add(kv.first, kv.second);
                            kwargs.push_back(std::make_pair(PycRef<ASTNode>(), rest.cast<ASTNode>()));
                        }
                    }
                }
                PycRef<ASTNode> call = new ASTCall(func,
                        ASTCall::pparam_t(args.begin(), args.end()), kwargs);
                stack.push(call);
            }
            break;
        case Pyc::CALL_METHOD_A:
            {
                ASTCall::pparam_t pparamList;
                for (int i = 0; i < operand; i++) {
                    PycRef<ASTNode> param = stack.top();
                    stack.pop();
                    if (param.type() == ASTNode::NODE_FUNCTION) {
                        PycRef<ASTNode> fun_code = param.cast<ASTFunction>()->code();
                        PycRef<PycCode> code_src = fun_code.cast<ASTObject>()->object().cast<PycCode>();
                        PycRef<PycString> function_name = code_src->name();
                        if (function_name->isEqual("<lambda>")) {
                            pparamList.push_front(param);
                        } else {
                            // Decorator used
                            PycRef<ASTNode> decor_name = new ASTName(function_name);
                            curblock->append(new ASTStore(param, decor_name));

                            pparamList.push_front(decor_name);
                        }
                    } else {
                        pparamList.push_front(param);
                    }
                }
                PycRef<ASTNode> func = stack.top();
                stack.pop();
                stack.push(new ASTCall(func, pparamList, ASTCall::kwparam_t()));
            }
            break;
        case Pyc::CONTINUE_LOOP_A:
            curblock->append(new ASTKeyword(ASTKeyword::KW_CONTINUE));
            break;
        case Pyc::COMPARE_OP_A:
            {
                PycRef<ASTNode> right = stack.top();
                stack.pop();
                PycRef<ASTNode> left = stack.top();
                stack.pop();
                auto arg = operand;
                if (mod->verCompare(3, 12) == 0)
                    arg >>= 4; // changed under GH-100923
                else if (mod->verCompare(3, 13) >= 0)
                    arg >>= 5;
                stack.push(ast_chain_compare(chainLeft, chainMiddle, left, right, arg));
            }
            break;
        case Pyc::CONTAINS_OP_A:
            {
                PycRef<ASTNode> right = stack.top();
                stack.pop();
                PycRef<ASTNode> left = stack.top();
                stack.pop();
                // `(name := value) in seq` is one chain kept as a value, not an assignment
                if (left != nullptr && left.type() == ASTNode::NODE_CHAINSTORE
                        && left.cast<ASTChainStore>()->nodes().size() == 1)
                    left.cast<ASTChainStore>()->setExpression(true);
                // The operand will be 0 for 'in' and 1 for 'not in'.
                stack.push(ast_chain_compare(chainLeft, chainMiddle, left, right,
                        operand ? ASTCompare::CMP_NOT_IN : ASTCompare::CMP_IN));
            }
            break;
        case Pyc::DELETE_ATTR_A:
            {
                PycRef<ASTNode> name = stack.top();
                stack.pop();
                curblock->append(new ASTDelete(new ASTBinary(name, new ASTName(code->getName(operand)), ASTBinary::BIN_ATTR)));
            }
            break;
        case Pyc::DELETE_GLOBAL_A:
            code->markGlobal(code->getName(operand));
            /* Fall through */
        case Pyc::DELETE_NAME_A:
            {
                PycRef<PycString> varname = code->getName(operand);

                if (varname->length() >= 2 && varname->value()[0] == '_'
                        && varname->value()[1] == '[') {
                    /* Don't show deletes that are a result of list comps. */
                    break;
                }

                PycRef<ASTNode> name = new ASTName(varname);
                if (isExceptVarDelete(curblock, name))
                    break;
                curblock->append(new ASTDelete(name));
            }
            break;
        case Pyc::DELETE_FAST_A:
            {
                PycRef<ASTNode> name;

                if (mod->verCompare(1, 3) < 0)
                    name = new ASTName(code->getName(operand));
                else
                    name = new ASTName(code->getLocal(operand));

                if (name.cast<ASTName>()->name()->value()[0] == '_'
                        && name.cast<ASTName>()->name()->value()[1] == '[') {
                    /* Don't show deletes that are a result of list comps. */
                    break;
                }

                if (isExceptVarDelete(curblock, name))
                    break;

                curblock->append(new ASTDelete(name));
            }
            break;
        case Pyc::DELETE_SLICE_0:
            {
                PycRef<ASTNode> name = stack.top();
                stack.pop();

                curblock->append(new ASTDelete(new ASTSubscr(name, new ASTSlice(ASTSlice::SLICE0))));
            }
            break;
        case Pyc::DELETE_SLICE_1:
            {
                PycRef<ASTNode> upper = stack.top();
                stack.pop();
                PycRef<ASTNode> name = stack.top();
                stack.pop();

                curblock->append(new ASTDelete(new ASTSubscr(name, new ASTSlice(ASTSlice::SLICE1, upper))));
            }
            break;
        case Pyc::DELETE_SLICE_2:
            {
                PycRef<ASTNode> lower = stack.top();
                stack.pop();
                PycRef<ASTNode> name = stack.top();
                stack.pop();

                curblock->append(new ASTDelete(new ASTSubscr(name, new ASTSlice(ASTSlice::SLICE2, NULL, lower))));
            }
            break;
        case Pyc::DELETE_SLICE_3:
            {
                PycRef<ASTNode> lower = stack.top();
                stack.pop();
                PycRef<ASTNode> upper = stack.top();
                stack.pop();
                PycRef<ASTNode> name = stack.top();
                stack.pop();

                curblock->append(new ASTDelete(new ASTSubscr(name, new ASTSlice(ASTSlice::SLICE3, upper, lower))));
            }
            break;
        case Pyc::DELETE_SUBSCR:
            {
                PycRef<ASTNode> key = stack.top();
                stack.pop();
                PycRef<ASTNode> name = stack.top();
                stack.pop();

                curblock->append(new ASTDelete(new ASTSubscr(name, key)));
            }
            break;
        case Pyc::DUP_TOP:
            {
                if (stack.top().type() == PycObject::TYPE_NULL) {
                    // None is a null slot; the mark, not pointer equality, makes the later store a chain
                    stack.push(stack.top(), curpos);
                } else if (mod->verCompare(3, 8) >= 0
                        && stack.top().type() == ASTNode::NODE_CHAINSTORE
                        && stack.top().cast<ASTChainStore>()->expression()) {
                    // Nested (y := (x := ...)) copies the inner named expression
                    stack.push(stack.top(), curpos);
                } else if (stack.top().type() == ASTNode::NODE_CHAINSTORE) {
                    int chainAt = stack.top_dup_at();
                    auto chainstore = stack.top();
                    stack.pop();
                    stack.push(stack.top(), curpos);
                    stack.push(chainstore, chainAt);
                } else {
                    stack.push(stack.top(), curpos);
                    ASTNodeList::list_t targets;
                    stack.push(new ASTChainStore(targets, stack.top()));
                }
            }
            break;
        case Pyc::DUP_TOP_TWO:
            {
                PycRef<ASTNode> first = stack.top();
                stack.pop();
                PycRef<ASTNode> second = stack.top();

                stack.push(first);
                stack.push(second);
                stack.push(first);
            }
            break;
        case Pyc::DUP_TOPX_A:
            {
                std::stack<PycRef<ASTNode> > first;
                std::stack<PycRef<ASTNode> > second;

                for (int i = 0; i < operand; i++) {
                    PycRef<ASTNode> node = stack.top();
                    stack.pop();
                    first.push(node);
                    second.push(node);
                }

                while (first.size()) {
                    stack.push(first.top());
                    first.pop();
                }

                while (second.size()) {
                    stack.push(second.top());
                    second.pop();
                }
            }
            break;
        case Pyc::RERAISE:
        case Pyc::RERAISE_A:
            // 3.9-3.10 RERAISE ending an except chain plays the role of END_FINALLY; elsewhere it is cleanup
            if (!(mod->verCompare(3, 9) >= 0 && mod->verCompare(3, 11) < 0
                    && (curblock->blktype() == ASTBlock::BLK_EXCEPT
                        || curblock->blktype() == ASTBlock::BLK_FINALLY)))
                break;
            // fall through
        case Pyc::END_FINALLY:
            {
                bool isFinally = false;
                int tryExitPastHandlers = 0;
                if (curblock->blktype() == ASTBlock::BLK_FINALLY) {
                    PycRef<ASTBlock> final = curblock;
                    blocks.pop();

                    stack = stack_hist.top();
                    stack_hist.pop();

                    curblock = blocks.top();
                    curblock->append(final.cast<ASTNode>());
                    isFinally = true;
                } else if (curblock->blktype() == ASTBlock::BLK_EXCEPT) {
                    blocks.pop();
                    PycRef<ASTBlock> prev = curblock;

                    bool isUninitAsyncFor = false;
                    if (blocks.top()->blktype() == ASTBlock::BLK_CONTAINER) {
                        auto container = blocks.top();
                        blocks.pop();
                        auto asyncForBlock = blocks.top();
                        isUninitAsyncFor = asyncForBlock->blktype() == ASTBlock::BLK_ASYNCFOR && !asyncForBlock->inited();
                        if (isUninitAsyncFor) {
                            auto tryBlock = container->nodes().front().cast<ASTBlock>();
                            if (!tryBlock->nodes().empty() && tryBlock->blktype() == ASTBlock::BLK_TRY) {
                                auto store = tryBlock->nodes().front().try_cast<ASTStore>();
                                if (store) {
                                    asyncForBlock.cast<ASTIterBlock>()->setIndex(store->dest());
                                }
                            }
                            curblock = blocks.top();
                            stack = stack_hist.top();
                            stack_hist.pop();
                            if (!curblock->inited())
                                fprintf(stderr, "Error when decompiling 'async for'.\n");
                        } else {
                            blocks.push(container);
                        }
                    }

                    if (!isUninitAsyncFor) {
                        if (curblock->size() != 0) {
                            blocks.top()->append(curblock.cast<ASTNode>());
                        }

                        curblock = blocks.top();

                        // The inlined else was appended before the excepts; the handler chain ends here
                        if (curblock->blktype() == ASTBlock::BLK_CONTAINER) {
                            PycRef<ASTContainerBlock> cont = curblock.cast<ASTContainerBlock>();
                            if (py310InlinedElseHandlers.erase(cont->except()))
                                ast_py310_else_after_except(cont);
                        }

                        /* Turn it into an else statement. */
                        // try/except has an else only when a handler exit jumps past the try body's target (just after END_FINALLY)
                        int elseEnd = 0;
                        if (curblock->blktype() == ASTBlock::BLK_CONTAINER
                                && curblock.cast<ASTContainerBlock>()->hasExcept())
                            elseEnd = ast_handler_exit_target(code, mod,
                                    curblock.cast<ASTContainerBlock>()->except(), curpos);
                        bool contHasFinally = curblock->blktype() == ASTBlock::BLK_CONTAINER
                                && curblock.cast<ASTContainerBlock>()->hasFinally();
                        // The try body must resume right after the handlers for this to be its own else clause
                        int tryExit = curblock->blktype() == ASTBlock::BLK_CONTAINER ? curblock->end() : 0;
                        if (tryExit > pos)
                            tryExitPastHandlers = tryExit;
                        if ((elseEnd > pos && tryExit <= pos) || contHasFinally) {
                            PycRef<ASTBlock> elseblk = new ASTBlock(ASTBlock::BLK_ELSE,
                                    elseEnd > pos ? elseEnd : prev->end());
                            elseblk->init();
                            blocks.push(elseblk);
                            curblock = blocks.top();
                        }
                        else {
                            stack = stack_hist.top();
                            stack_hist.pop();
                        }
                    }
                }

                if (curblock->blktype() == ASTBlock::BLK_CONTAINER) {
                    /* This marks the end of the except block(s). */
                    PycRef<ASTContainerBlock> cont = curblock.cast<ASTContainerBlock>();
                    if (py310InlinedElseHandlers.erase(cont->except()))
                        ast_py310_else_after_except(cont);
                    if (!cont->hasFinally() || isFinally) {
                        /* If there's no finally block, pop the container. */
                        blocks.pop();
                        curblock = blocks.top();
                        curblock->append(cont.cast<ASTNode>());
                    }
                }
                // if-body ending in try/except: its exits jump over the if's else, which starts right here
                if (tryExitPastHandlers > pos && blocks.size() > 1 && curblock->end() == pos
                        && (curblock->blktype() == ASTBlock::BLK_IF
                            || curblock->blktype() == ASTBlock::BLK_ELIF)) {
                    PycRef<ASTBlock> ifblk = curblock;
                    blocks.pop();
                    blocks.top()->append(ifblk.cast<ASTNode>());
                    if (!stack_hist.empty()) {
                        stack = stack_hist.top();
                        stack_hist.pop();
                    }
                    stack_hist.push(stack);
                    PycRef<ASTBlock> elseblk = new ASTBlock(ASTBlock::BLK_ELSE, tryExitPastHandlers);
                    if (ifblk->inited() == ASTCondBlock::PRE_POPPED)
                        elseblk->init(ASTCondBlock::PRE_POPPED);
                    blocks.push(elseblk);
                    curblock = blocks.top();
                }
            }
            break;
        case Pyc::EXEC_STMT:
            {
                if (stack.top().type() == ASTNode::NODE_CHAINSTORE) {
                    stack.pop();
                }
                PycRef<ASTNode> loc = stack.top();
                stack.pop();
                PycRef<ASTNode> glob = stack.top();
                stack.pop();
                PycRef<ASTNode> stmt = stack.top();
                stack.pop();

                curblock->append(new ASTExec(stmt, glob, loc));
            }
            break;
        case Pyc::FOR_ITER_A:
        case Pyc::INSTRUMENTED_FOR_ITER_A:
            {
                PycRef<ASTNode> iter = stack.top(); // Iterable
                if (mod->verCompare(3, 12) < 0) {
                    // Do not pop the iterator for py 3.12+
                    stack.pop();
                }
                /* Pop it? Don't pop it? */

                int end;
                bool comprehension = false;

                // before 3.8, there is a SETUP_LOOP instruction with block start and end position,
                //    the operand is usually a jump to a POP_BLOCK instruction
                // after 3.8, block extent has to be inferred implicitly; the operand is a jump to a position after the for block
                if (mod->majorVer() == 3 && mod->minorVer() >= 8) {
                    end = operand;
                    if (mod->verCompare(3, 10) >= 0)
                        end *= sizeof(uint16_t); // // BPO-27129
                    end += pos;
                    // 3.12+ jumps are relative to the end of the inline cache
                    if (mod->verCompare(3, 12) >= 0)
                        end = ast_relative_jump_target(mod, opcode, operand, pos, false);
                    {
                        const char* cn = code->name()->value();
                        comprehension = cn && (!strcmp(cn, "<listcomp>")
                                || !strcmp(cn, "<setcomp>")
                                || !strcmp(cn, "<dictcomp>"));
                    }
                    if (inlineCompActive)
                        comprehension = true;
                } else {
                    PycRef<ASTBlock> top = blocks.top();
                    end = top->end(); // block end position from SETUP_LOOP
                    const char* cn = code->name() != nullptr ? code->name()->value() : "";
                    if (top->blktype() == ASTBlock::BLK_WHILE) {
                        blocks.pop();
                    } else if (!strcmp(cn, "<genexpr>")) {
                        // Generator expression body is a plain yielding loop ending at the FOR_ITER target
                        end = pos + operand;
                    } else {
                        comprehension = true;
                    }
                }

                PycRef<ASTIterBlock> forblk = new ASTIterBlock(ASTBlock::BLK_FOR, curpos, end, iter);
                forblk->setComprehension(comprehension);
                blocks.push(forblk.cast<ASTBlock>());
                curblock = blocks.top();
                if (mod->verCompare(3, 12) >= 0 && !comprehension)
                    forBlockAt[curpos] = forblk.cast<ASTBlock>();
                if (comprehension && inlineCompActive)
                    inlineCompMaxLoopDepth = std::max(inlineCompMaxLoopDepth,
                            ++inlineCompLoopDepth);

                stack.push(NULL);
            }
            break;
        case Pyc::FOR_LOOP_A:
            {
                PycRef<ASTNode> curidx = stack.top(); // Current index
                stack.pop();
                PycRef<ASTNode> iter = stack.top(); // Iterable
                stack.pop();

                bool comprehension = false;
                PycRef<ASTBlock> top = blocks.top();
                if (top->blktype() == ASTBlock::BLK_WHILE) {
                    blocks.pop();
                } else {
                    comprehension = true;
                }
                PycRef<ASTIterBlock> forblk = new ASTIterBlock(ASTBlock::BLK_FOR, curpos, top->end(), iter);
                forblk->setComprehension(comprehension);
                blocks.push(forblk.cast<ASTBlock>());
                curblock = blocks.top();

                /* Python Docs say:
                      "push the sequence, the incremented counter,
                       and the current item onto the stack." */
                stack.push(iter);
                stack.push(curidx);
                stack.push(NULL); // We can totally hack this >_>
            }
            break;
        case Pyc::GET_AITER:
            {
                if (mod->verCompare(3, 11) < 0) {
                    PycRef<ASTNode> iter = stack.empty() ? nullptr : stack.top();
                    if (!stack.empty())
                        stack.pop();
                    PycRef<ASTBlock> top = blocks.top();
                    if (top->blktype() == ASTBlock::BLK_WHILE) {
                        blocks.pop();
                        PycRef<ASTIterBlock> forblk = new ASTIterBlock(ASTBlock::BLK_ASYNCFOR, curpos, top->end(), iter);
                        blocks.push(forblk.cast<ASTBlock>());
                        curblock = blocks.top();
                        stack.push(nullptr);
                    } else {
                        fprintf(stderr, "Unsupported use of GET_AITER outside of SETUP_LOOP\n");
                    }
                    break;
                }
                // Statement form is GET_AITER immediately followed by GET_ANEXT.
                // A call consumes the iterator as an async-comp argument, and an
                // inlined comp (3.12-3.14) starts the loop at a later GET_ANEXT.
                if (!ast_next_real_is(code, mod, pos, Pyc::GET_ANEXT))
                    break;
                if (stack.empty()) {
                    cleanBuild = false;
                    break;
                }
                PycRef<ASTNode> iter = stack.top();
                int anext = pos;
                int op = 0, arg = 0, next = 0, at = pos;
                while (code->code() != nullptr
                        && ast_read_wordcode_instr(code->code(), mod, at, op, arg, next)) {
                    if (op == Pyc::GET_ANEXT) {
                        anext = at;
                        break;
                    }
                    at = next;
                }
                bool comprehension = inlineCompActive || ast_is_comp_code(code);
                if (blocks.size() > 1 && blocks.top()->blktype() == ASTBlock::BLK_WHILE)
                    blocks.pop();
                PycRef<ASTIterBlock> forblk = new ASTIterBlock(
                        ASTBlock::BLK_ASYNCFOR, anext, ast_async_for_end(code, mod, pos), iter);
                forblk->setComprehension(comprehension);
                blocks.push(forblk.cast<ASTBlock>());
                curblock = blocks.top();
                if (comprehension && inlineCompActive)
                    inlineCompMaxLoopDepth = std::max(inlineCompMaxLoopDepth, ++inlineCompLoopDepth);
                // 3.12+ inline comps keep the iterator under the element placeholder, like FOR_ITER
                if (comprehension && mod->verCompare(3, 12) >= 0)
                    stack.push(NULL);
                else {
                    stack.pop();
                    stack.push(iter);
                }
            }
            break;
        case Pyc::GET_ANEXT:
            // Loop head when GET_AITER was not the previous instruction (inlined comp, or a <listcomp> body)
            if (mod->verCompare(3, 11) < 0
                    || (curblock != nullptr && curblock->blktype() == ASTBlock::BLK_ASYNCFOR))
                break;
            if (stack.empty()) {
                cleanBuild = false;
                break;
            }
            {
                PycRef<ASTNode> iter = stack.top();
                bool comprehension = inlineCompActive || ast_is_comp_code(code);
                if (mod->verCompare(3, 12) < 0)
                    stack.pop();
                PycRef<ASTIterBlock> forblk = new ASTIterBlock(
                        ASTBlock::BLK_ASYNCFOR, curpos, ast_async_for_end(code, mod, pos), iter);
                forblk->setComprehension(comprehension);
                blocks.push(forblk.cast<ASTBlock>());
                curblock = blocks.top();
                if (comprehension && inlineCompActive)
                    inlineCompMaxLoopDepth = std::max(inlineCompMaxLoopDepth, ++inlineCompLoopDepth);
                stack.push(NULL);
            }
            break;
        case Pyc::FORMAT_VALUE_A:
            {
                auto conversion_flag = static_cast<ASTFormattedValue::ConversionFlag>(operand);
                PycRef<ASTNode> format_spec = nullptr;
                if (conversion_flag & ASTFormattedValue::HAVE_FMT_SPEC) {
                    format_spec = stack.top();
                    stack.pop();
                }
                auto val = stack.top();
                stack.pop();
                stack.push(new ASTFormattedValue(val, conversion_flag, format_spec));
            }
            break;
        case Pyc::FORMAT_SIMPLE:
            {
                PycRef<ASTNode> val = stack.top();
                stack.pop();
                if (val.type() == ASTNode::NODE_FORMATTEDVALUE)
                    stack.push(val);
                else
                    stack.push(new ASTFormattedValue(val, ASTFormattedValue::NONE, nullptr));
            }
            break;
        case Pyc::SET_ADD_A:
            {
                PycRef<ASTNode> value = stack.top();
                stack.pop();
                if (curblock->blktype() == ASTBlock::BLK_FOR
                        && curblock.cast<ASTIterBlock>()->isComprehension()) {
                    ASTSet::value_t values;
                    values.emplace_back(value);
                    if (!stack.empty())
                        stack.pop();
                    stack.push(new ASTComprehension(new ASTSet(values)));
                    break;
                }

                PycRef<ASTNode> target = stack.top(operand);
                if (target != nullptr && target.type() == ASTNode::NODE_SET) {
                    target.cast<ASTSet>()->add(value);
                } else if (mod->verCompare(3, 14) >= 0
                        && target != nullptr && target.type() == ASTNode::NODE_NAME
                        && target.cast<ASTName>()->name()->isEqual(
                                "__conditional_annotations__")) {
                    /* Compiler bookkeeping for deferred annotations. */
                    suppressNextPopTop = true;
                } else if (curblock != nullptr) {
                    cleanBuild = false;
                    curblock->append(new ASTUnsupported("# unsupported SET_ADD target"));
                }
            }
            break;
        case Pyc::FORMAT_WITH_SPEC:
            {
                PycRef<ASTNode> format_spec = stack.top();
                stack.pop();
                PycRef<ASTNode> val = stack.top();
                stack.pop();
                if (val.type() == ASTNode::NODE_FORMATTEDVALUE) {
                    PycRef<ASTFormattedValue> formatted = val.cast<ASTFormattedValue>();
                    stack.push(new ASTFormattedValue(formatted->val(),
                            static_cast<ASTFormattedValue::ConversionFlag>(
                                    formatted->conversion() | ASTFormattedValue::HAVE_FMT_SPEC),
                            format_spec));
                } else {
                    stack.push(new ASTFormattedValue(val, ASTFormattedValue::HAVE_FMT_SPEC,
                            format_spec));
                }
            }
            break;
        case Pyc::CONVERT_VALUE_A:
            {
                PycRef<ASTNode> val = stack.top();
                stack.pop();
                stack.push(new ASTFormattedValue(val,
                        static_cast<ASTFormattedValue::ConversionFlag>(operand), nullptr));
            }
            break;
        case Pyc::GET_AWAITABLE:
        case Pyc::GET_AWAITABLE_A:
            {
                // 3.11+ operand selects await / aenter / aexit; the value is still the awaited expression
                if (stack.empty()) {
                    cleanBuild = false;
                    break;
                }
                PycRef<ASTNode> object = stack.top();
                stack.pop();
                if (opcode == Pyc::GET_AWAITABLE_A && operand != 0) {
                    fprintf(stderr, "Warning: async with protocol in %s (offset %d)\n",
                            code->name() != nullptr ? code->name()->value() : "<unknown>", curpos);
                    cleanBuild = false;
                }
                // The await around an async comprehension is the compiler's coroutine call, not source
                if (object != nullptr && object.type() == ASTNode::NODE_COMPREHENSION) {
                    stack.push(object);
                    break;
                }
                stack.push(new ASTAwaitable(object));
            }
            break;
        case Pyc::GET_ITER:
            {
                // 3.15 yield from is GET_ITER; LOAD const; SEND, not GET_YIELD_FROM_ITER
                if (mod->verCompare(3, 11) >= 0 && code->code() != nullptr && !stack.empty()) {
                    int op = 0, arg = 0, next = 0, at = pos, steps = 0;
                    bool yieldFrom = false;
                    while (steps < 4 && ast_read_wordcode_instr(code->code(), mod, at, op, arg, next)) {
                        if (op == Pyc::CACHE || op == Pyc::PUSH_NULL
                                || op == Pyc::LOAD_CONST_A || op == Pyc::LOAD_COMMON_CONSTANT_A)
                            at = next;
                        else {
                            yieldFrom = op == Pyc::SEND_A;
                            break;
                        }
                        steps++;
                    }
                    if (yieldFrom) {
                        PycRef<ASTNode> object = stack.top();
                        stack.pop();
                        stack.push(new ASTAwaitable(object, true));
                    }
                }
            }
            break;
        case Pyc::GET_YIELD_FROM_ITER:
            {
                // 3.11+ has no YIELD_FROM opcode; the following SEND loop is the yield-from
                if (mod->verCompare(3, 11) < 0)
                    break;
                if (stack.empty()) {
                    cleanBuild = false;
                    break;
                }
                PycRef<ASTNode> object = stack.top();
                stack.pop();
                stack.push(new ASTAwaitable(object, true));
            }
            break;
        case Pyc::IMPORT_NAME_A:
            if (mod->majorVer() == 1) {
                stack.push(new ASTImport(new ASTName(code->getName(operand)), NULL));
            } else {
                PycRef<ASTNode> fromlist = stack.top();
                stack.pop();
                int level = 0;
                if (mod->verCompare(2, 5) >= 0) {
                    PycRef<ASTNode> levelnode = stack.top();
                    stack.pop();
                    if (levelnode.type() == ASTNode::NODE_OBJECT) {
                        PycRef<PycObject> obj = levelnode.cast<ASTObject>()->object();
                        if (obj->type() == PycObject::TYPE_INT)
                            level = obj.cast<PycInt>()->value();
                    }
                }
                // 3.15+ IMPORT_NAME: bits 0-1 are lazy/eager flags, name index in bits 2+
                int nameIdx = operand;
                bool lazy = false;
                if (mod->verCompare(3, 15) >= 0) {
                    lazy = (operand & 1) != 0;
                    nameIdx = operand >> 2;
                }
                PycRef<ASTImport> import = new ASTImport(new ASTName(code->getName(nameIdx)),
                                                         fromlist, level);
                import->setLazy(lazy);
                stack.push(import.cast<ASTNode>());
            }
            break;
        case Pyc::IMPORT_FROM_A:
            {
                // `import a.b as c` (fromlist None) walks submodules with IMPORT_FROM: keep importing the dotted module
                PycRef<ASTImport> module = stack.top().try_cast<ASTImport>();
                PycRef<ASTObject> fromlist;
                if (module != nullptr)
                    fromlist = module->fromlist().try_cast<ASTObject>();
                bool noFromlist = module != nullptr && (module->fromlist() == nullptr
                        || (fromlist != nullptr && fromlist->object() != nullptr
                            && fromlist->object().type() == PycObject::TYPE_NONE));
                if (noFromlist) {
                    module->setProcessed();
                    PycRef<ASTImport> alias = new ASTImport(module->name(), module->fromlist(), module->level());
                    alias->setLazy(module->lazy());
                    alias->setModuleAlias(true);
                    alias->setProcessed();
                    stack.push(alias.cast<ASTNode>());
                    break;
                }
                stack.push(new ASTName(code->getName(operand)));
            }
            break;
        case Pyc::IMPORT_STAR:
            {
                PycRef<ASTNode> import = stack.top();
                stack.pop();
                curblock->append(new ASTStore(import, NULL));
            }
            break;
        case Pyc::CALL_INTRINSIC_1_A:
            {
                if (operand == 2) {
                    PycRef<ASTNode> import = stack.top();
                    stack.pop();
                    curblock->append(new ASTStore(import, NULL));
                } else if (operand == 3) {
                    /* INTRINSIC_STOPITERATION_ERROR wraps a generator's return
                       path at runtime; it has no source-level representation. */
                } else if (operand == 4) {
                    // INTRINSIC_ASYNC_GEN_WRAP marks an async generator; no source form
                } else if (operand == 6) {
                    // INTRINSIC_LIST_TO_TUPLE (3.12+): *args list becomes a tuple
                    PycRef<ASTNode> list = stack.top();
                    stack.pop();
                    if (list.type() == ASTNode::NODE_LIST) {
                        const auto& lv = list.cast<ASTList>()->values();
                        stack.push(new ASTTuple(ASTTuple::value_t(lv.begin(), lv.end())));
                    } else {
                        stack.push(list);
                    }
                } else {
                    PycRef<ASTNode> arg = stack.top();
                    stack.pop();
                    cleanBuild = false;
                    curblock->append(new ASTUnsupported(std::string("# unsupported CALL_INTRINSIC_1 ") +
                                     std::to_string(operand)));
                    stack.push(arg);
                }
            }
            break;
        case Pyc::CALL_INTRINSIC_2_A:
            {
                PycRef<ASTNode> right = stack.top();
                stack.pop();
                PycRef<ASTNode> left = stack.top();
                stack.pop();
                (void)right;
                stack.push(left);
                cleanBuild = false;
                curblock->append(new ASTUnsupported(std::string("# unsupported CALL_INTRINSIC_2 ") +
                                 std::to_string(operand)));
            }
            break;
        case Pyc::IS_OP_A:
            {
                PycRef<ASTNode> right = stack.top();
                stack.pop();
                PycRef<ASTNode> left = stack.top();
                stack.pop();
                // The operand will be 0 for 'is' and 1 for 'is not'.
                stack.push(ast_chain_compare(chainLeft, chainMiddle, left, right,
                        operand ? ASTCompare::CMP_IS_NOT : ASTCompare::CMP_IS));
            }
            break;
        case Pyc::JUMP_IF_FALSE_A:
        case Pyc::JUMP_IF_TRUE_A:
        case Pyc::JUMP_IF_FALSE_OR_POP_A:
        case Pyc::JUMP_IF_TRUE_OR_POP_A:
        case Pyc::JUMP_IF_NOT_EXC_MATCH_A:
        case Pyc::POP_JUMP_IF_FALSE_A:
        case Pyc::POP_JUMP_IF_TRUE_A:
        case Pyc::POP_JUMP_IF_NONE_A:
        case Pyc::POP_JUMP_IF_NOT_NONE_A:
        case Pyc::POP_JUMP_FORWARD_IF_FALSE_A:
        case Pyc::POP_JUMP_FORWARD_IF_TRUE_A:
        case Pyc::POP_JUMP_FORWARD_IF_NONE_A:
        case Pyc::POP_JUMP_FORWARD_IF_NOT_NONE_A:
        case Pyc::INSTRUMENTED_POP_JUMP_IF_FALSE_A:
        case Pyc::INSTRUMENTED_POP_JUMP_IF_TRUE_A:
        case Pyc::INSTRUMENTED_POP_JUMP_IF_NONE_A:
        case Pyc::INSTRUMENTED_POP_JUMP_IF_NOT_NONE_A:
            {
                if (whileAmbiguous.erase(curpos)) {
                    fprintf(stderr, "Warning: ambiguous while condition in %s (offset %d)\n",
                            code->name() != nullptr ? code->name()->value() : "<unknown>", curpos);
                    cleanBuild = false;
                }
                if (whileLatchGuards.count(curpos)) {
                    if (!stack.empty())
                        stack.pop();
                    break;
                }
                // 3.10 backward POP_JUMP_IF_* that ScanWhileLoops recorded closes the loop
                if (mod->verCompare(3, 10) == 0 && whileBackedges.count(curpos)) {
                    if (ast_close_while_backedge(blocks, curblock, stack, whileDupSkip,
                            curpos, source, mod, opcode, operand, pos)) {
                        std::map<int, int>::iterator el = whileElseAt.find(curpos);
                        if (el != whileElseAt.end() && el->second > pos) {
                            stack_hist.push(stack);
                            PycRef<ASTBlock> elseblk = new ASTBlock(ASTBlock::BLK_ELSE, el->second);
                            elseblk->init();
                            blocks.push(elseblk);
                            curblock = blocks.top();
                        }
                        break;
                    }
                }
                // 3.9-3.10 JUMP_IF_NOT_EXC_MATCH pops the type and the exception, like COMPARE_OP exception match + POP_JUMP_IF_FALSE
                if (opcode == Pyc::JUMP_IF_NOT_EXC_MATCH_A) {
                    PycRef<ASTNode> excType = stack.top();
                    stack.pop();
                    PycRef<ASTNode> exc = stack.top();
                    stack.pop();
                    stack.push(new ASTCompare(exc, excType, ASTCompare::CMP_EXCEPTION));
                }
                /* Python 3.11 while-loop entry guard: open a BLK_WHILE here
                   instead of an if. The matching back-edge (POP_JUMP_BACKWARD)
                   closes it. */
                auto wit = whileGuardEnd.find(curpos);
                if (wit != whileGuardEnd.end()) {
                    if (stack.empty()) {
                        cleanBuild = false;
                        break;
                    }
                    PycRef<ASTNode> wcond = stack.top();
                    stack.pop();
                    bool wneg = false;
                    if (opcode == Pyc::POP_JUMP_FORWARD_IF_NONE_A) {
                        wcond = new ASTCompare(wcond, new ASTObject(Pyc_None),
                                               ASTCompare::CMP_IS_NOT);
                    } else if (opcode == Pyc::POP_JUMP_FORWARD_IF_NOT_NONE_A) {
                        wcond = new ASTCompare(wcond, new ASTObject(Pyc_None),
                                               ASTCompare::CMP_IS);
                    } else if (opcode == Pyc::POP_JUMP_IF_TRUE_A
                            || opcode == Pyc::POP_JUMP_FORWARD_IF_TRUE_A
                            || opcode == Pyc::INSTRUMENTED_POP_JUMP_IF_TRUE_A) {
                        wneg = true;
                    }
                    // Inverted entry guard: the condition holds on entry; skip the exit jump to the body
                    auto inv = whileInvertedGuards.find(curpos);
                    if (inv != whileInvertedGuards.end()) {
                        wneg = !wneg;
                        while (pos < inv->second && !source.atEof()) {
                            curpos = pos;
                            bc_next(source, mod, opcode, operand, pos);
                        }
                    }
                    PycRef<ASTCondBlock> wh = new ASTCondBlock(
                            ASTBlock::BLK_WHILE, wit->second, wcond, wneg);
                    wh->init(ASTCondBlock::PRE_POPPED);
                    blocks.push(wh.cast<ASTBlock>());
                    curblock = blocks.top();
                    break;
                }

                PycRef<ASTNode> cond = stack.top();
                PycRef<ASTNode> rawCond = cond;
                PycRef<ASTCondBlock> ifblk;
                int popped = ASTCondBlock::UNINITED;
                // `if cond: break` folded into one conditional jump to the while exit
                if (mod->verCompare(3, 8) >= 0 && cond != nullptr && opcode != Pyc::JUMP_IF_FALSE_OR_POP_A
                        && opcode != Pyc::JUMP_IF_TRUE_OR_POP_A && opcode != Pyc::JUMP_IF_NOT_EXC_MATCH_A
                        && !whileCondJumps.count(curpos)
                        && !(curblock->blktype() == ASTBlock::BLK_WHILE && curblock->size() == 0
                                && curblock.cast<ASTCondBlock>()->cond() != nullptr)
                        && !(stack.size() >= 2 && stack.top(2) == cond)) {
                    bool relative = mod->verCompare(3, 12) >= 0 || opcode == Pyc::POP_JUMP_FORWARD_IF_FALSE_A
                            || opcode == Pyc::POP_JUMP_FORWARD_IF_TRUE_A || opcode == Pyc::POP_JUMP_FORWARD_IF_NONE_A
                            || opcode == Pyc::POP_JUMP_FORWARD_IF_NOT_NONE_A;
                    int target = relative ? ast_relative_jump_target(mod, opcode, operand, pos, false)
                            : (mod->verCompare(3, 10) >= 0 ? operand * (int)sizeof(uint16_t) : operand);
                    if (target > curpos && ast_is_while_exit_jump(blocks, target)) {
                        stack.pop();
                        PycRef<ASTNode> test = cond;
                        if (opcode == Pyc::POP_JUMP_IF_NONE_A || opcode == Pyc::POP_JUMP_FORWARD_IF_NONE_A)
                            test = new ASTCompare(cond, new ASTObject(Pyc_None), ASTCompare::CMP_IS);
                        else if (opcode == Pyc::POP_JUMP_IF_NOT_NONE_A || opcode == Pyc::POP_JUMP_FORWARD_IF_NOT_NONE_A)
                            test = new ASTCompare(cond, new ASTObject(Pyc_None), ASTCompare::CMP_IS_NOT);
                        else if (opcode != Pyc::POP_JUMP_IF_TRUE_A && opcode != Pyc::POP_JUMP_FORWARD_IF_TRUE_A
                                && opcode != Pyc::INSTRUMENTED_POP_JUMP_IF_TRUE_A && opcode != Pyc::JUMP_IF_TRUE_A)
                            test = ast_negate_condition(cond);
                        PycRef<ASTCondBlock> ifblk = new ASTCondBlock(ASTBlock::BLK_IF, curpos, test, false);
                        ifblk->init(ASTCondBlock::PRE_POPPED);
                        ifblk->append(new ASTKeyword(ASTKeyword::KW_BREAK));
                        curblock->append(ifblk.cast<ASTNode>());
                        break;
                    }
                }

                // Chained comparison: the jump tests `a < b` while the copied `b` below waits for the next comparison
                if ((opcode == Pyc::JUMP_IF_FALSE_OR_POP_A || opcode == Pyc::POP_JUMP_IF_FALSE_A
                            || opcode == Pyc::POP_JUMP_FORWARD_IF_FALSE_A)
                        && cond != nullptr && cond.type() == ASTNode::NODE_COMPARE && stack.size() >= 2) {
                    bool copied = stack.size() >= 3 && stack.top(2) == cond;
                    PycRef<ASTNode> middle = stack.top(copied ? 3 : 2);
                    if (middle != nullptr && middle == cond.cast<ASTCompare>()->right()) {
                        bool relative = opcode == Pyc::POP_JUMP_FORWARD_IF_FALSE_A || mod->verCompare(3, 11) >= 0;
                        int target = relative ? ast_relative_jump_target(mod, opcode, operand, pos, false)
                                : (mod->verCompare(3, 10) >= 0 ? operand * (int)sizeof(uint16_t) : operand);
                        stack.pop();
                        if (copied) {
                            stack.pop();
                            skipNextPopTop = true;
                        }
                        chainLeft = cond;
                        chainMiddle = middle;
                        ast_register_chain_cleanup(code, mod, pos, target, chainSkipAt);
                        break;
                    }
                }

                // 3.12+ value `a or b`: COPY 1; [TO_BOOL;] POP_JUMP_IF_TRUE end; POP_TOP; b
                bool py314CopiedShortCircuit = mod->verCompare(3, 12) >= 0
                        && (opcode == Pyc::POP_JUMP_IF_FALSE_A
                                || opcode == Pyc::POP_JUMP_IF_TRUE_A)
                        && cond != nullptr && stack.top(2) == cond;

                // 2.7-3.11 value `a or b` / `a and b`: keep the left operand and combine it at the jump target
                if (opcode == Pyc::JUMP_IF_TRUE_OR_POP_A || opcode == Pyc::JUMP_IF_FALSE_OR_POP_A) {
                    int target = mod->verCompare(3, 11) >= 0
                            ? ast_relative_jump_target(mod, opcode, operand, pos, false)
                            : (mod->verCompare(3, 10) >= 0 ? operand * (int)sizeof(uint16_t) : operand);
                    ASTBinary::BinOp op = opcode == Pyc::JUMP_IF_TRUE_OR_POP_A
                            ? ASTBinary::BIN_LOG_OR : ASTBinary::BIN_LOG_AND;
                    ast_push_short_circuit(py314ShortCircuitAt[target], op, stack);
                    break;
                }

                if (opcode == Pyc::POP_JUMP_FORWARD_IF_NONE_A
                        || opcode == Pyc::POP_JUMP_FORWARD_IF_NOT_NONE_A) {
                    /* Python 3.11: compare TOS against None, then pop and jump.
                       IF_NONE jumps past the body when TOS is None, so the body
                       runs for "x is not None" (and vice-versa). */
                    stack.pop();
                    ASTCompare::CompareOp cmpop =
                        (opcode == Pyc::POP_JUMP_FORWARD_IF_NONE_A)
                        ? ASTCompare::CMP_IS_NOT
                        : ASTCompare::CMP_IS;
                    cond = new ASTCompare(cond, new ASTObject(Pyc_None), cmpop);
                    popped = ASTCondBlock::PRE_POPPED;
                }

                if (opcode == Pyc::POP_JUMP_IF_FALSE_A
                        || opcode == Pyc::JUMP_IF_NOT_EXC_MATCH_A
                        || opcode == Pyc::POP_JUMP_IF_TRUE_A
                        || opcode == Pyc::POP_JUMP_IF_NONE_A
                        || opcode == Pyc::POP_JUMP_IF_NOT_NONE_A
                        || opcode == Pyc::POP_JUMP_FORWARD_IF_FALSE_A
                        || opcode == Pyc::POP_JUMP_FORWARD_IF_TRUE_A
                        || opcode == Pyc::INSTRUMENTED_POP_JUMP_IF_FALSE_A
                        || opcode == Pyc::INSTRUMENTED_POP_JUMP_IF_TRUE_A
                        || opcode == Pyc::INSTRUMENTED_POP_JUMP_IF_NONE_A
                        || opcode == Pyc::INSTRUMENTED_POP_JUMP_IF_NOT_NONE_A) {
                    /* Pop condition before the jump */
                    stack.pop();
                    popped = ASTCondBlock::PRE_POPPED;
                }

                if (opcode == Pyc::POP_JUMP_IF_NONE_A
                        || opcode == Pyc::INSTRUMENTED_POP_JUMP_IF_NONE_A) {
                    cond = new ASTCompare(cond, new ASTObject(Pyc_None),
                            mod->verCompare(3, 14) >= 0
                            ? ASTCompare::CMP_IS_NOT : ASTCompare::CMP_IS);
                } else if (opcode == Pyc::POP_JUMP_IF_NOT_NONE_A
                        || opcode == Pyc::INSTRUMENTED_POP_JUMP_IF_NOT_NONE_A) {
                    cond = new ASTCompare(cond, new ASTObject(Pyc_None),
                            mod->verCompare(3, 14) >= 0
                            ? ASTCompare::CMP_IS : ASTCompare::CMP_IS_NOT);
                }

                /* Store the current stack for the else statement(s) */
                stack_hist.push(stack);

                if (opcode == Pyc::JUMP_IF_FALSE_OR_POP_A
                        || opcode == Pyc::JUMP_IF_TRUE_OR_POP_A) {
                    /* Pop condition only if condition is met */
                    stack.pop();
                    popped = ASTCondBlock::POPPED;
                }

                /* "Jump if true" means "Jump if not false" */
                bool neg = opcode == Pyc::JUMP_IF_TRUE_A
                        || opcode == Pyc::JUMP_IF_TRUE_OR_POP_A
                        || opcode == Pyc::POP_JUMP_IF_TRUE_A
                        || opcode == Pyc::POP_JUMP_FORWARD_IF_TRUE_A
                        || opcode == Pyc::INSTRUMENTED_POP_JUMP_IF_TRUE_A;

                int offs = operand;
                if (mod->verCompare(3, 10) >= 0)
                    offs *= sizeof(uint16_t); // // BPO-27129
                if (mod->verCompare(3, 12) >= 0
                        || opcode == Pyc::JUMP_IF_FALSE_A
                        || opcode == Pyc::JUMP_IF_TRUE_A
                        || opcode == Pyc::POP_JUMP_FORWARD_IF_TRUE_A
                        || opcode == Pyc::POP_JUMP_FORWARD_IF_FALSE_A
                        || opcode == Pyc::POP_JUMP_FORWARD_IF_NONE_A
                        || opcode == Pyc::POP_JUMP_FORWARD_IF_NOT_NONE_A) {
                    /* Offset is relative in these cases */
                    offs = ast_relative_jump_target(mod, opcode, operand, pos, false);
                }
                if (mod->verCompare(3, 12) >= 0
                        && (opcode == Pyc::POP_JUMP_IF_TRUE_A
                            || opcode == Pyc::POP_JUMP_IF_FALSE_A
                            || opcode == Pyc::POP_JUMP_FORWARD_IF_TRUE_A
                            || opcode == Pyc::POP_JUMP_FORWARD_IF_FALSE_A)) {
                    /* At the tail of a for body CPython can emit two adjacent
                       JUMP_BACKWARD instructions to the same loop header: one
                       is an explicit `continue`, the other is normal loop
                       fallthrough.  In that degenerate shape the source if
                       condition describes the taken jump, not the fallthrough
                       region used by the normal reconstruction rule. */
                    auto readBackedgeTarget = [&](int at, int& target) {
                        int op = 0, arg = 0, after = 0;
                        do {
                            if (!ast_read_wordcode_instr(code->code(), mod, at,
                                    op, arg, after))
                                return false;
                            at = after;
                        } while (op == Pyc::CACHE || op == Pyc::NOT_TAKEN
                                || op == Pyc::INSTRUMENTED_NOT_TAKEN_A);
                        if (op != Pyc::JUMP_BACKWARD_A
                                && op != Pyc::JUMP_BACKWARD_NO_INTERRUPT_A
                                && op != Pyc::INSTRUMENTED_JUMP_BACKWARD_A)
                            return false;
                        target = ast_relative_jump_target(mod, op, arg, after,
                                true);
                        return true;
                    };
                    int fallthroughTarget = -1, takenTarget = -2;
                    if (readBackedgeTarget(pos, fallthroughTarget)
                            && readBackedgeTarget(offs, takenTarget)
                            && fallthroughTarget == takenTarget) {
                        neg = opcode == Pyc::POP_JUMP_IF_FALSE_A
                                || opcode == Pyc::POP_JUMP_FORWARD_IF_FALSE_A;
                    }
                }
                if (py314CopiedShortCircuit) {
                    if (!stack_hist.empty())
                        stack_hist.pop();
                    skipNextPopTop = true;
                    // The jump already popped the copy; the original stays as the left operand (its POP_TOP is skipped)
                    ast_push_short_circuit(py314ShortCircuitAt[offs], opcode == Pyc::POP_JUMP_IF_TRUE_A
                            ? ASTBinary::BIN_LOG_OR : ASTBinary::BIN_LOG_AND, stack);
                    break;
                }

                if (opcode == Pyc::JUMP_IF_NOT_EXC_MATCH_A && exceptSetups.empty()
                        && curblock->blktype() == ASTBlock::BLK_FINALLY
                        && blocks.size() > 1) {
                    blocks.pop();
                    curblock = blocks.top();

                    if (curblock->blktype() == ASTBlock::BLK_CONTAINER) {
                        PycRef<ASTContainerBlock> cont = curblock.cast<ASTContainerBlock>();
                        cont->setFinally(0);
                        cont->setExcept(offs);
                        if (cont->size() != 0 && cont->nodes().back().type() == ASTNode::NODE_BLOCK
                                && cont->nodes().back().cast<ASTBlock>()->blktype() == ASTBlock::BLK_FINALLY) {
                            cont->removeLast();
                        }
                    }
                } else if (opcode == Pyc::JUMP_IF_NOT_EXC_MATCH_A && exceptSetups.empty()
                        && curblock->blktype() == ASTBlock::BLK_CONTAINER) {
                    PycRef<ASTContainerBlock> cont = curblock.cast<ASTContainerBlock>();
                    if (cont->hasFinally()) {
                        cont->setFinally(0);
                        cont->setExcept(offs);
                    }
                    if (cont->size() != 0 && cont->nodes().back().type() == ASTNode::NODE_BLOCK
                            && cont->nodes().back().cast<ASTBlock>()->blktype() == ASTBlock::BLK_FINALLY) {
                        cont->removeLast();
                    }
                }

                /* Chained comparison: if this conditional jump lands on a
                   trampoline (POP_TOP; JUMP_FORWARD exit), resolve it to the
                   real exit so both halves of `a == b == c` share a target and
                   merge with `and` rather than `or`. */
                {
                    auto tit = trampolineExit.find(offs);
                    if (tit != trampolineExit.end())
                        offs = tit->second;
                }

                // A walrus while whose second test returns through a copy of the same exit is still `and`
                PycRef<ASTChainStore> walrusCond = curblock->blktype() == ASTBlock::BLK_WHILE
                        ? curblock.cast<ASTCondBlock>()->cond().try_cast<ASTChainStore>() : nullptr;
                if (walrusCond != nullptr && walrusCond->expression() && curblock->size() == 0
                        && offs > curpos && offs < curblock->end() && code->code() != nullptr) {
                    int span = curblock->end() - offs;
                    const char* retBytes = code->code()->value();
                    int retLen = code->code()->length();
                    if (span >= 4 && span <= 16 && (span % 2) == 0
                            && curblock->end() + span <= retLen
                            && memcmp(retBytes + offs, retBytes + curblock->end(), span) == 0)
                        offs = curblock->end();
                }

                if (cond.type() == ASTNode::NODE_COMPARE
                        && cond.cast<ASTCompare>()->op() == ASTCompare::CMP_EXCEPTION) {
                    int except_end = offs;
                    PycBuffer target_source(code->code()->value(), code->code()->length());
                    int target_opcode = 0, target_operand = 0, target_pos = offs;
                    if (target_source.setPos(offs)) {
                        bc_next(target_source, mod, target_opcode, target_operand, target_pos);
                        if (target_opcode == Pyc::RETURN_VALUE
                                || target_opcode == Pyc::RETURN_CONST_A
                                || target_opcode == Pyc::INSTRUMENTED_RETURN_VALUE_A
                                || target_opcode == Pyc::INSTRUMENTED_RETURN_CONST_A) {
                            /* Python 3.13 can dispatch a failed exception match to
                               a return that terminates the current clause.
                               Keep that return inside the except block. */
                            except_end = target_pos;
                        }
                    } else {
                        cleanBuild = false;
                    }
                    if (curblock->blktype() == ASTBlock::BLK_EXCEPT
                            && curblock.cast<ASTCondBlock>()->cond() == NULL) {
                        /* Refining the initial (type-less) except handler. The
                           clause ends at the dispatch jump target (the next
                           clause / reraise), not at the whole handler region;
                           using the region end would swallow following clauses
                           when this clause does not fall through (e.g. raises). */
                        if (offs <= pos)
                            except_end = curblock->end();
                        blocks.pop();
                        curblock = blocks.top();

                        stack_hist.pop();
                    }

                    ifblk = new ASTCondBlock(ASTBlock::BLK_EXCEPT, except_end, cond.cast<ASTCompare>()->right(), false);
                    py311_except_bind_pending = mod->verCompare(3, 11) >= 0;
                } else if (curblock->blktype() == ASTBlock::BLK_ELSE
                           && curblock->size() == 0) {
                    /* Collapse into elif statement */
                    int elseEnd = curblock->end();
                    blocks.pop();
                    stack = stack_hist.top();
                    stack_hist.pop();
                    ifblk = new ASTCondBlock(ASTBlock::BLK_ELIF, offs, cond, neg);
                    // The elif test can skip less than the else did (its body ends in raise/return): the rest is its else
                    if (offs > curpos && offs < elseEnd)
                        elifElseEnd[offs] = std::make_pair(ifblk.cast<ASTBlock>(), elseEnd);
                } else if (curblock->size() == 0 && !curblock->inited()
                           && curblock->blktype() == ASTBlock::BLK_WHILE) {
                    /* The condition for a while loop */
                    PycRef<ASTBlock> top = blocks.top();
                    blocks.pop();
                    ifblk = new ASTCondBlock(top->blktype(), offs, cond, neg);

                    /* We don't store the stack for loops! Pop it! */
                    stack_hist.pop();
                } else if (curblock->size() == 0 && curblock->end() <= offs
                           && (curblock->blktype() == ASTBlock::BLK_IF
                           || curblock->blktype() == ASTBlock::BLK_ELIF
                           || curblock->blktype() == ASTBlock::BLK_WHILE)
                           // A first test skipping to a separate branch (after an unconditional jump) is a nested if, not `or`
                           && !(curblock->end() < offs && curblock->end() > pos
                                && ast_follows_unconditional_exit(code, mod, curpos, curblock->end()))) {
                    PycRef<ASTNode> newcond;
                    PycRef<ASTCondBlock> top = curblock.cast<ASTCondBlock>();
                    PycRef<ASTNode> cond1 = ast_condition_body(top->cond(), top->negative());
                    PycRef<ASTNode> cond2 = ast_condition_body(cond, neg);
                    blocks.pop();

                    if (curblock->blktype() == ASTBlock::BLK_WHILE) {
                        if (!stack_hist.empty())
                            stack_hist.pop();
                        else
                            cleanBuild = false;
                    } else {
                        if (stack_hist.size() >= 2) {
                            FastStack s_top = stack_hist.top();
                            stack_hist.pop();
                            stack_hist.pop();
                            stack_hist.push(s_top);
                        } else if (!stack_hist.empty()) {
                            cleanBuild = false;
                            FastStack s_top = stack_hist.top();
                            stack_hist.pop();
                            stack_hist.push(s_top);
                        } else {
                            cleanBuild = false;
                        }
                    }

                    if (curblock->end() == offs
                            || (curblock->end() == curpos && !top->negative())) {
                        /* if blah and blah */
                        if (top->shortCircuitOrTarget() > pos
                                && cond1.type() == ASTNode::NODE_BINARY
                                && cond1.cast<ASTBinary>()->op() == ASTBinary::BIN_LOG_OR) {
                            /* Python 3.13 emits the first true branch of
                               `a or b and c` directly to the body, while the
                               `b` path continues into `c`. Reassociate only
                               this recorded short-circuit shape; an explicit
                               `(a or b) and c` instead jumps to the third
                               condition and never sets the marker. */
                            PycRef<ASTBinary> orcond = cond1.cast<ASTBinary>();
                            newcond = new ASTBinary(orcond->left(),
                                    new ASTBinary(orcond->right(), cond2,
                                                  ASTBinary::BIN_LOG_AND),
                                    ASTBinary::BIN_LOG_OR);
                        } else {
                            newcond = new ASTBinary(cond1, cond2, ASTBinary::BIN_LOG_AND);
                        }
                    } else {
                        /* if blah or blah */
                        newcond = new ASTBinary(ast_negate_condition(cond1),
                                                cond2, ASTBinary::BIN_LOG_OR);
                    }
                    ifblk = new ASTCondBlock(top->blktype(), offs, newcond, false);
                    if (mod->verCompare(3, 13) >= 0 && curblock->end() != offs)
                        ifblk->setShortCircuitOrTarget(top->end());
                } else if (curblock->blktype() == ASTBlock::BLK_FOR
                            && curblock.cast<ASTIterBlock>()->isComprehension()
                            && mod->verCompare(2, 7) >= 0) {
                    /* Comprehension condition */
                    // Repeated filters (if a if b) compile like `if a and b`
                    PycRef<ASTIterBlock> compFor = curblock.cast<ASTIterBlock>();
                    // Kept items: the jump condition if the fall-through returns to the loop head, else its negation
                    PycRef<ASTNode> filter = ast_condition_body(cond, neg);
                    int afterOp = 0, afterArg = 0, afterAt = pos, afterNext = 0;
                    while (ast_read_wordcode_instr(code->code(), mod, afterAt, afterOp, afterArg, afterNext)
                            && (afterOp == Pyc::CACHE || afterOp == Pyc::NOT_TAKEN))
                        afterAt = afterNext;
                    bool fallthroughSkips = (afterOp == Pyc::JUMP_BACKWARD_A
                                || afterOp == Pyc::JUMP_ABSOLUTE_A)
                            && (afterOp == Pyc::JUMP_ABSOLUTE_A
                                ? afterArg * (mod->verCompare(3, 10) >= 0 ? 2 : 1)
                                : ast_relative_jump_target(mod, afterOp, afterArg, afterNext, true))
                                == compFor->start();
                    bool jumpSkips = offs == compFor->start();
                    if (fallthroughSkips != jumpSkips) {
                        PycRef<ASTNode> taken;
                        if (opcode == Pyc::POP_JUMP_IF_NONE_A || opcode == Pyc::POP_JUMP_FORWARD_IF_NONE_A
                                || opcode == Pyc::INSTRUMENTED_POP_JUMP_IF_NONE_A)
                            taken = new ASTCompare(rawCond, new ASTObject(Pyc_None),
                                    jumpSkips ? ASTCompare::CMP_IS_NOT : ASTCompare::CMP_IS);
                        else if (opcode == Pyc::POP_JUMP_IF_NOT_NONE_A
                                || opcode == Pyc::POP_JUMP_FORWARD_IF_NOT_NONE_A
                                || opcode == Pyc::INSTRUMENTED_POP_JUMP_IF_NOT_NONE_A)
                            taken = new ASTCompare(rawCond, new ASTObject(Pyc_None),
                                    jumpSkips ? ASTCompare::CMP_IS : ASTCompare::CMP_IS_NOT);
                        else {
                            bool jumpIfTrue = opcode == Pyc::POP_JUMP_IF_TRUE_A
                                    || opcode == Pyc::POP_JUMP_FORWARD_IF_TRUE_A
                                    || opcode == Pyc::INSTRUMENTED_POP_JUMP_IF_TRUE_A
                                    || opcode == Pyc::JUMP_IF_TRUE_A
                                    || opcode == Pyc::JUMP_IF_TRUE_OR_POP_A;
                            taken = (jumpIfTrue == jumpSkips) ? ast_negate_condition(rawCond) : rawCond;
                        }
                        filter = taken;
                    }
                    if (compFor->condition() != nullptr)
                        compFor->setCondition(new ASTBinary(compFor->condition(), filter,
                                ASTBinary::BIN_LOG_AND));
                    else
                        compFor->setCondition(filter);
                    stack_hist.pop();
                    // TODO: Handle older python versions, where condition
                    // is laid out a little differently.
                    break;
                } else {
                    /* Plain old if statement */
                    ifblk = new ASTCondBlock(ASTBlock::BLK_IF, offs, cond, neg);
                    // Nested if whose false exit is threaded through the enclosing branch's closing jump: it ends at that jump
                    int closeJump = -1;
                    if ((curblock->blktype() == ASTBlock::BLK_IF || curblock->blktype() == ASTBlock::BLK_ELIF
                                || curblock->blktype() == ASTBlock::BLK_ELSE)
                            && curblock->end() > pos && curblock->end() < offs
                            && ast_closing_jump_to(code, mod, pos, curblock->end(), offs, closeJump))
                        ifblk->setEnd(closeJump);
                }

                if (popped)
                    ifblk->init(popped);

                blocks.push(ifblk.cast<ASTBlock>());
                curblock = blocks.top();
            }
            break;
        case Pyc::POP_JUMP_BACKWARD_IF_TRUE_A:
        case Pyc::POP_JUMP_BACKWARD_IF_FALSE_A:
        case Pyc::POP_JUMP_BACKWARD_IF_NONE_A:
        case Pyc::POP_JUMP_BACKWARD_IF_NOT_NONE_A:
            {
                /* Python 3.11 while-loop back-edge: the duplicate condition has
                   just been evaluated onto the stack; discard it and close the
                   BLK_WHILE opened at the matching entry guard. Only act when a
                   BLK_WHILE is actually open (guard against a misidentified
                   back-edge collapsing the whole block stack). */
                if (whileBackedges.count(curpos)
                        && ast_close_while_backedge(blocks, curblock, stack, whileDupSkip,
                                curpos, source, mod, opcode, operand, pos))
                    break;

                /* Python 3.11: conditional jump backwards. In compiled loops
                   this implements an in-body guard ("if cond: <rest of body>")
                   where a failed test jumps back to the loop header to start the
                   next iteration. Model it as an if-block that spans to the end
                   of the enclosing loop body. */
                PycRef<ASTNode> cond = stack.top();
                stack.pop();

                // 3.11 comprehension filter: conditional jump back to the comprehension's FOR_ITER
                if (curblock->blktype() == ASTBlock::BLK_FOR
                        && curblock.cast<ASTIterBlock>()->isComprehension()
                        && ast_relative_jump_target(mod, opcode, operand, pos, true)
                            == curblock.cast<ASTIterBlock>()->start()) {
                    PycRef<ASTNode> filter = cond;
                    if (opcode == Pyc::POP_JUMP_BACKWARD_IF_TRUE_A)
                        filter = ast_negate_condition(cond);
                    else if (opcode == Pyc::POP_JUMP_BACKWARD_IF_NONE_A)
                        filter = new ASTCompare(cond, new ASTObject(Pyc_None), ASTCompare::CMP_IS_NOT);
                    else if (opcode == Pyc::POP_JUMP_BACKWARD_IF_NOT_NONE_A)
                        filter = new ASTCompare(cond, new ASTObject(Pyc_None), ASTCompare::CMP_IS);
                    PycRef<ASTIterBlock> compFor = curblock.cast<ASTIterBlock>();
                    compFor->setCondition(compFor->condition() != nullptr
                            ? new ASTBinary(compFor->condition(), filter, ASTBinary::BIN_LOG_AND)
                            : filter);
                    break;
                }

                bool neg = false;
                if (opcode == Pyc::POP_JUMP_BACKWARD_IF_NONE_A) {
                    /* jumps back when "x is None" -> body runs for "x is not None" */
                    cond = new ASTCompare(cond, new ASTObject(Pyc_None), ASTCompare::CMP_IS_NOT);
                } else if (opcode == Pyc::POP_JUMP_BACKWARD_IF_NOT_NONE_A) {
                    cond = new ASTCompare(cond, new ASTObject(Pyc_None), ASTCompare::CMP_IS);
                } else if (opcode == Pyc::POP_JUMP_BACKWARD_IF_TRUE_A) {
                    /* jumps back when cond is true -> body runs for "not cond" */
                    neg = true;
                }

                int end = curblock->end();

                stack_hist.push(stack);
                PycRef<ASTCondBlock> ifblk =
                        new ASTCondBlock(ASTBlock::BLK_IF, end, cond, neg);
                ifblk->init(ASTCondBlock::PRE_POPPED);
                blocks.push(ifblk.cast<ASTBlock>());
                curblock = blocks.top();
            }
            break;
        case Pyc::JUMP_ABSOLUTE_A:
        // bpo-47120: Replaced JUMP_ABSOLUTE by the relative jump JUMP_BACKWARD.
        case Pyc::JUMP_BACKWARD_A:
        case Pyc::JUMP_BACKWARD_NO_INTERRUPT_A:
        case Pyc::INSTRUMENTED_JUMP_BACKWARD_A:
            {
                int offs = operand;
                if ((opcode == Pyc::JUMP_BACKWARD_A
                            || opcode == Pyc::JUMP_BACKWARD_NO_INTERRUPT_A
                            || opcode == Pyc::INSTRUMENTED_JUMP_BACKWARD_A)
                        && mod->verCompare(3, 11) >= 0) {
                    offs = ast_relative_jump_target(mod, opcode, operand, pos, true);
                } else if (mod->verCompare(3, 10) >= 0) {
                    offs *= sizeof(uint16_t); // // BPO-27129
                }

                // Back-edge ending a re-opened loop fragment: the loop is already attached to its parent
                if (reopenedLoop != nullptr && curblock == reopenedLoop
                        && offs == reopenedLoop.cast<ASTIterBlock>()->start()) {
                    if (!stack.empty() && stack.top() == reopenedLoop.cast<ASTIterBlock>()->iter())
                        stack.pop();
                    blocks.pop();
                    curblock = blocks.top();
                    reopenedLoop = nullptr;
                    break;
                }

                if (whileBackedges.count(curpos)) {
                    while (blocks.size() > 1
                            && curblock->blktype() != ASTBlock::BLK_WHILE) {
                        PycRef<ASTBlock> inner = curblock;
                        blocks.pop();
                        curblock = blocks.top();
                        curblock->append(inner.cast<ASTNode>());
                    }
                    if (curblock->blktype() == ASTBlock::BLK_WHILE
                            && blocks.size() > 1) {
                        PycRef<ASTBlock> wh = curblock;
                        blocks.pop();
                        curblock = blocks.top();
                        curblock->append(wh.cast<ASTNode>());
                    }
                    // Skip the duplicated exit block placed after the back-edge
                    auto dup = whileDupSkip.find(curpos);
                    while (dup != whileDupSkip.end() && pos < dup->second && !source.atEof()) {
                        curpos = pos;
                        bc_next(source, mod, opcode, operand, pos);
                    }
                    break;
                }

                if (mod->verCompare(3, 11) >= 0
                        && curblock->blktype() == ASTBlock::BLK_EXCEPT
                        && !activeDeferredExceptContainers.empty()
                        && blocks.size() > 2) {
                    PycRef<ASTBlock> except = curblock;
                    std::stack<PycRef<ASTBlock> > pending = blocks;
                    pending.pop();
                    PycRef<ASTBlock> container = pending.top();
                    if (container->blktype() == ASTBlock::BLK_CONTAINER
                            && container == activeDeferredExceptContainers.back().cast<ASTBlock>()) {
                        bool jumpsToLoopStart = false;
                        auto recordedLoop = deferredHandlerLoopStart.find(
                                container.cast<ASTContainerBlock>()->except());
                        if (recordedLoop != deferredHandlerLoopStart.end())
                            jumpsToLoopStart = recordedLoop->second == offs;
                        pending.pop();
                        while (!jumpsToLoopStart && !pending.empty()) {
                            PycRef<ASTBlock> enclosing = pending.top();
                            if (enclosing->blktype() == ASTBlock::BLK_FOR
                                    || enclosing->blktype() == ASTBlock::BLK_ASYNCFOR) {
                                jumpsToLoopStart = enclosing.cast<ASTIterBlock>()->start() == offs;
                                break;
                            }
                            pending.pop();
                        }
                        // Handler deferred after its loop was closed: a back-edge to a FOR_ITER still targets the loop head
                        int headOp = 0, headArg = 0, headNext = 0;
                        if (!jumpsToLoopStart && ast_read_wordcode_instr(code->code(), mod, offs, headOp, headArg, headNext)
                                && headOp == Pyc::FOR_ITER_A)
                            jumpsToLoopStart = true;
                        // The handler's back-edge is implicit only when nothing follows the try in the loop body
                        if (jumpsToLoopStart && ast_code_follows_try(code, mod, exception_entries,
                                    container.cast<ASTContainerBlock>()->except(), offs, blocks))
                            except->append(new ASTKeyword(ASTKeyword::KW_CONTINUE));

                        blocks.pop();
                        curblock = blocks.top();
                        if (!stack_hist.empty()) {
                            stack = stack_hist.top();
                            stack_hist.pop();
                        }
                        curblock->append(except.cast<ASTNode>());
                        // Another except clause follows at this clause's no-match target: keep the try statement open
                        int nextOp = 0, nextArg = 0, nextAt = except->end(), afterNext = 0;
                        while (nextAt > 0 && ast_read_wordcode_instr(code->code(), mod, nextAt,
                                    nextOp, nextArg, afterNext) && nextOp == Pyc::CACHE)
                            nextAt = afterNext;
                        if (except->end() > pos && nextOp != Pyc::RERAISE && nextOp != Pyc::RERAISE_A
                                && except.cast<ASTCondBlock>()->cond() != nullptr)
                            break;
                        blocks.pop();
                        curblock = blocks.top();
                        activeDeferredExceptContainers.pop_back();
                        break;
                    }
                }
                if (mod->verCompare(3, 8) >= 0 && offs > curpos && ast_is_while_exit_jump(blocks, offs)) {
                    ast_emit_for_break(blocks, curblock, stack, stack_hist, curpos);
                    break;
                }
                if (mod->verCompare(3, 8) >= 0 && mod->verCompare(3, 12) < 0
                        && offs > curpos && ast_is_for_exit_jump(blocks, curpos, offs, code, mod, forElse)) {
                    if (forElse)
                        forElseEnd[ast_innermost_for(blocks).cast<ASTIterBlock>()->start()] = forElse;
                    ast_emit_for_break(blocks, curblock, stack, stack_hist, curpos);
                    break;
                }
                // Pre-3.11 try body whose normal exit jumps back to the loop head: continue ends the try, then the handlers follow
                if (offs < pos && mod->verCompare(3, 11) < 0
                        && curblock->blktype() == ASTBlock::BLK_CONTAINER
                        && curblock.cast<ASTContainerBlock>()->hasExcept()
                        && !curblock->nodes().empty()
                        && curblock->nodes().back().type() == ASTNode::NODE_BLOCK
                        && curblock->nodes().back().cast<ASTBlock>()->blktype() == ASTBlock::BLK_TRY) {
                    if (!ast_pre311_try_is_loop_tail(code, mod, curblock.cast<ASTContainerBlock>()->except(), offs, blocks))
                        curblock->nodes().back().cast<ASTBlock>()->append(new ASTKeyword(ASTKeyword::KW_CONTINUE));
                    int loopEnd = 0;
                    std::stack<PycRef<ASTBlock> > pending = blocks;
                    while (!pending.empty() && !loopEnd) {
                        int bt = pending.top()->blktype();
                        if (bt == ASTBlock::BLK_FOR || bt == ASTBlock::BLK_WHILE || bt == ASTBlock::BLK_ASYNCFOR)
                            loopEnd = pending.top()->end();
                        pending.pop();
                    }
                    stack_hist.push(stack);
                    curblock->setEnd(loopEnd);
                    PycRef<ASTBlock> except = new ASTCondBlock(ASTBlock::BLK_EXCEPT, loopEnd, NULL, false);
                    except->init();
                    blocks.push(except);
                    curblock = blocks.top();
                    break;
                }
                // Pre-3.12 back-edge at the end of a for body: ifs still open there (false branch -> loop head) end with it
                if (offs < pos && mod->verCompare(3, 12) < 0
                        && (curblock->blktype() == ASTBlock::BLK_IF
                            || curblock->blktype() == ASTBlock::BLK_ELIF
                            || curblock->blktype() == ASTBlock::BLK_ELSE)) {
                    PycRef<ASTBlock> loop = ast_innermost_for(blocks);
                    if (loop != nullptr && offs == loop.cast<ASTIterBlock>()->start()
                            && pos == loop->end()) {
                        while (curblock != loop && blocks.size() > 1
                                && (curblock->blktype() == ASTBlock::BLK_IF
                                    || curblock->blktype() == ASTBlock::BLK_ELIF
                                    || curblock->blktype() == ASTBlock::BLK_ELSE)) {
                            PycRef<ASTBlock> done = curblock;
                            blocks.pop();
                            curblock = blocks.top();
                            if (!(done->blktype() == ASTBlock::BLK_ELSE && done->nodes().empty()))
                                curblock->append(done.cast<ASTNode>());
                            if (!stack_hist.empty()) {
                                stack = stack_hist.top();
                                stack_hist.pop();
                            }
                        }
                    }
                }
                if (offs < pos) {
                    if (curblock->blktype() == ASTBlock::BLK_FOR
                            || (mod->verCompare(3, 11) >= 0
                                && curblock->blktype() == ASTBlock::BLK_ASYNCFOR)) {
                        // offs is already absolute; a jump to the loop start at the body end closes the loop, earlier ones are continue
                        bool is_jump_to_start =
                                offs == curblock.cast<ASTIterBlock>()->start();
                        // 3.12+ back-edge right before END_FOR is the implicit iteration; END_FOR closes the loop
                        if (is_jump_to_start && mod->verCompare(3, 12) >= 0) {
                            int nextOp = 0, nextArg = 0, nextAt = pos, after = 0;
                            while (ast_read_wordcode_instr(code->code(), mod, nextAt, nextOp, nextArg, after)
                                    && nextOp == Pyc::CACHE)
                                nextAt = after;
                            if (nextOp == Pyc::END_FOR || nextOp == Pyc::INSTRUMENTED_END_FOR_A)
                                is_jump_to_start = false;
                            // Try body leaving the iteration while its handler resumes in code placed behind it: explicit continue
                            PycRef<ASTBlock> tryBody = ast_last_try_body(curblock);
                            if (!is_jump_to_start && tryBody != nullptr
                                    && ast_handler_exits_to_fragment(code, mod, exception_entries,
                                            curblock->nodes().back().cast<ASTContainerBlock>()->except(),
                                            forBlockAt, curblock)) {
                                tryBody->append(new ASTKeyword(ASTKeyword::KW_CONTINUE));
                                break;
                            }
                        }
                        bool at_loop_end = (curblock->end() != 0)
                                && ast_next_instr_offset_after_caches(mod, opcode, pos) == curblock->end();
                        bool should_pop_for_block = curblock.cast<ASTIterBlock>()->isComprehension();
                        if (should_pop_for_block && inlineCompActive
                                && stack.top().type() != ASTNode::NODE_COMPREHENSION)
                            break;
                        // in v3.8, SETUP_LOOP is deprecated and for blocks aren't terminated by POP_BLOCK, so we add them here
                        bool should_add_for_block = mod->majorVer() == 3 && mod->minorVer() >= 8
                                && is_jump_to_start
                                && (mod->verCompare(3, 11) < 0 || at_loop_end)
                                && !curblock.cast<ASTIterBlock>()->isComprehension();
                        // Pre-3.8 generator expressions have no SETUP_LOOP/POP_BLOCK: the back-edge at the end closes the loop
                        if (mod->verCompare(3, 8) < 0 && is_jump_to_start && at_loop_end
                                && code->name() != nullptr && code->name()->isEqual("<genexpr>"))
                            should_add_for_block = true;

                        if (mod->verCompare(3, 11) >= 0
                                && !should_pop_for_block && !should_add_for_block
                                && is_jump_to_start && !at_loop_end
                                && !curblock.cast<ASTIterBlock>()->isComprehension()) {
                            // explicit continue; one that hops over an exception handler ends the preceding try body
                            PycRef<ASTBlock> dest = curblock;
                            bool handlerFollows = false;
                            for (const auto& entry : exception_entries)
                                handlerFollows = handlerFollows || entry.target == pos;
                            // Try statement last in the loop body: its exit back-edge precedes the handler, which only jumps back too
                            if (handlerFollows && !ast_handler_resumes_in_loop(code, mod, exception_entries, pos,
                                                                               curblock->end()))
                                break;
                            if (handlerFollows && !curblock->nodes().empty()
                                    && curblock->nodes().back().type() == ASTNode::NODE_BLOCK
                                    && curblock->nodes().back().cast<ASTBlock>()->blktype()
                                        == ASTBlock::BLK_CONTAINER) {
                                for (const auto& child : curblock->nodes().back().cast<ASTBlock>()->nodes()) {
                                    if (child.type() == ASTNode::NODE_BLOCK
                                            && child.cast<ASTBlock>()->blktype() == ASTBlock::BLK_TRY)
                                        dest = child.cast<ASTBlock>();
                                }
                            }
                            dest->append(new ASTKeyword(ASTKeyword::KW_CONTINUE));
                            break;
                        }

                        if (should_pop_for_block || should_add_for_block) {
                            PycRef<ASTNode> top = stack.top();

                            if (top.type() == ASTNode::NODE_COMPREHENSION) {
                                PycRef<ASTComprehension> comp = top.cast<ASTComprehension>();

                                comp->addGenerator(curblock.cast<ASTIterBlock>());
                            }

                            PycRef<ASTBlock> tmp = curblock;
                            blocks.pop();
                            curblock = blocks.top();
                            if (should_add_for_block) {
                                curblock->append(tmp.cast<ASTNode>());
                                // for-else: the code up to the recorded break target is the else clause
                                auto fe = forElseEnd.find(tmp.cast<ASTIterBlock>()->start());
                                if (fe != forElseEnd.end() && fe->second > pos) {
                                    stack_hist.push(stack);
                                    PycRef<ASTBlock> elseblk = new ASTBlock(ASTBlock::BLK_ELSE, fe->second);
                                    elseblk->init();
                                    blocks.push(elseblk);
                                    curblock = blocks.top();
                                }
                            }
                            if (should_pop_for_block && inlineCompActive
                                    && inlineCompLoopDepth > 0) {
                                inlineCompLoopDepth--;
                                inlineCompCleanupOps = 2;
                                // END_ASYNC_FOR is followed by SWAP/STORE of the saved local, not END_FOR/POP_TOP
                                if (tmp->blktype() == ASTBlock::BLK_ASYNCFOR)
                                    inlineCompCleanupOps = 0;
                                if (inlineCompLoopDepth == 0
                                        && stack.top().type() == ASTNode::NODE_COMPREHENSION) {
                                    PycRef<ASTNode> comp = stack.top();
                                    stack.pop();
                                    for (int i = 1; i < inlineCompMaxLoopDepth
                                            && !stack.empty(); i++)
                                        stack.pop();
                                    if (!stack.empty())
                                        stack.pop();
                                    stack.push(comp);
                                    inlineCompMaxLoopDepth = 0;
                                }
                            }
                        }
                    } else if (curblock->blktype() == ASTBlock::BLK_ELSE) {
                        /* A backward jump out of an else block is a `continue`
                           when it targets an enclosing loop and we are still
                           before that loop's end (the natural loop-back that
                           closes an else sits exactly at the loop end). Emit a
                           continue inside the else rather than closing it. */
                        if (mod->verCompare(3, 11) >= 0) {
                            int loopEnd = -1;
                            std::stack<PycRef<ASTBlock> > tmp = blocks;
                            while (!tmp.empty()) {
                                int bt = tmp.top()->blktype();
                                if (bt == ASTBlock::BLK_FOR
                                        || bt == ASTBlock::BLK_WHILE) {
                                    loopEnd = tmp.top()->end();
                                    break;
                                }
                                tmp.pop();
                            }
                            if (loopEnd > 0 && pos < loopEnd) {
                                curblock->append(
                                        new ASTKeyword(ASTKeyword::KW_CONTINUE));
                                break;
                            }
                        }
                        if (!stack_hist.empty()) {
                            stack = stack_hist.top();
                            stack_hist.pop();
                        }

                        blocks.pop();
                        blocks.top()->append(curblock.cast<ASTNode>());
                        curblock = blocks.top();

                        if (curblock->blktype() == ASTBlock::BLK_CONTAINER
                                && !curblock.cast<ASTContainerBlock>()->hasFinally()) {
                            blocks.pop();
                            blocks.top()->append(curblock.cast<ASTNode>());
                            curblock = blocks.top();
                        }
                    } else {
                        bool hasEnclosingLoop = false;
                        if (mod->verCompare(3, 11) >= 0) {
                            std::stack<PycRef<ASTBlock> > pending = blocks;
                            while (!pending.empty()) {
                                int type = pending.top()->blktype();
                                if (type == ASTBlock::BLK_FOR || type == ASTBlock::BLK_ASYNCFOR
                                        || type == ASTBlock::BLK_WHILE) {
                                    hasEnclosingLoop = true;
                                    break;
                                }
                                pending.pop();
                            }
                        }
                        // Pre-3.11 handler of the loop body's last try: its jump back is the implicit next iteration
                        bool implicitBack = false;
                        if (mod->verCompare(3, 11) < 0 && curblock->blktype() == ASTBlock::BLK_EXCEPT && blocks.size() > 1) {
                            std::stack<PycRef<ASTBlock> > pending = blocks;
                            pending.pop();
                            PycRef<ASTBlock> cont = pending.top();
                            implicitBack = cont->blktype() == ASTBlock::BLK_CONTAINER
                                    && cont.cast<ASTContainerBlock>()->hasExcept()
                                    && ast_pre311_try_is_loop_tail(code, mod, cont.cast<ASTContainerBlock>()->except(),
                                                                   offs, blocks);
                        }
                        // 3.11+ handler back-edge to the loop head (loop possibly closed already): a continue only when code follows the try
                        int headOp = 0, headArg = 0, headNext = 0;
                        if (mod->verCompare(3, 11) >= 0
                                && curblock->blktype() == ASTBlock::BLK_EXCEPT && blocks.size() > 1
                                && ast_read_wordcode_instr(code->code(), mod, offs, headOp, headArg, headNext)
                                && headOp == Pyc::FOR_ITER_A) {
                            std::stack<PycRef<ASTBlock> > pending = blocks;
                            pending.pop();
                            PycRef<ASTBlock> cont = pending.top();
                            if (cont->blktype() == ASTBlock::BLK_CONTAINER && cont.cast<ASTContainerBlock>()->hasExcept()) {
                                hasEnclosingLoop = ast_code_follows_try(code, mod, exception_entries,
                                        cont.cast<ASTContainerBlock>()->except(), offs, blocks);
                                implicitBack = !hasEnclosingLoop;
                            }
                        }
                        // Jump straight into the handler is the inlined finally's loop back-edge, not continue
                        bool implicitTail = false;
                        if (mod->verCompare(3, 11) < 0 && curblock->blktype() == ASTBlock::BLK_TRY
                                && blocks.size() > 1) {
                            std::stack<PycRef<ASTBlock> > pending = blocks;
                            pending.pop();
                            if (pending.top()->blktype() == ASTBlock::BLK_CONTAINER) {
                                PycRef<ASTContainerBlock> cont = pending.top().cast<ASTContainerBlock>();
                                int handler = cont->hasExcept() ? cont->except() : cont->finally();
                                int loopStart = 0;
                                std::stack<PycRef<ASTBlock> > loops = blocks;
                                while (!loops.empty() && !loopStart) {
                                    int bt = loops.top()->blktype();
                                    if (bt == ASTBlock::BLK_FOR || bt == ASTBlock::BLK_ASYNCFOR)
                                        loopStart = loops.top().cast<ASTIterBlock>()->start();
                                    loops.pop();
                                }
                                implicitTail = handler > 0 && pos == handler
                                        && loopStart != 0 && offs == loopStart;
                            }
                        }
                        if ((mod->verCompare(3, 11) < 0 || hasEnclosingLoop) && !implicitBack && !implicitTail)
                            curblock->append(new ASTKeyword(ASTKeyword::KW_CONTINUE));
                        else if (implicitBack && curblock->nodes().empty())
                            curblock->append(new ASTKeyword(ASTKeyword::KW_PASS));
                    }

                    /* We're in a loop, this jumps back to the start */
                    /* I think we'll just ignore this case... */
                    break; // Bad idea? Probably!
                }

                if (curblock->blktype() == ASTBlock::BLK_CONTAINER) {
                    PycRef<ASTContainerBlock> cont = curblock.cast<ASTContainerBlock>();
                    if (cont->hasExcept() && pos <= cont->except()) {
                        // Forward absolute jump over the handlers: record where the try body resumes
                        if (offs > pos)
                            cont->setEnd(offs);
                        PycRef<ASTBlock> except = new ASTCondBlock(ASTBlock::BLK_EXCEPT, 0, NULL, false);
                        except->init();
                        blocks.push(except);
                        curblock = blocks.top();
                    }
                    break;
                }

                if (!stack_hist.empty()) {
                    stack = stack_hist.top();
                    stack_hist.pop();
                } else {
                    fprintf(stderr, "Warning: Stack history is empty, something wrong might have happened\n");
                }

                PycRef<ASTBlock> prev = curblock;
                PycRef<ASTBlock> nil;
                bool push = true;

                if (blocks.size() <= 1) {
                    cleanBuild = false;
                    break;
                }

                do {
                    blocks.pop();

                    blocks.top()->append(prev.cast<ASTNode>());

                    if (prev->blktype() == ASTBlock::BLK_IF
                            || prev->blktype() == ASTBlock::BLK_ELIF) {
                        if (push) {
                            stack_hist.push(stack);
                        }
                        PycRef<ASTBlock> next = new ASTBlock(ASTBlock::BLK_ELSE, blocks.top()->end());
                        if (prev->inited() == ASTCondBlock::PRE_POPPED) {
                            next->init(ASTCondBlock::PRE_POPPED);
                        }

                        blocks.push(next.cast<ASTBlock>());
                        prev = nil;
                    } else if (prev->blktype() == ASTBlock::BLK_EXCEPT) {
                        if (push) {
                            stack_hist.push(stack);
                        }
                        PycRef<ASTBlock> next = new ASTCondBlock(ASTBlock::BLK_EXCEPT, blocks.top()->end(), NULL, false);
                        next->init();

                        blocks.push(next.cast<ASTBlock>());
                        prev = nil;
                    } else if (prev->blktype() == ASTBlock::BLK_ELSE) {
                        /* Special case */
                        prev = blocks.top();
                        if (!push) {
                            stack = stack_hist.top();
                            stack_hist.pop();
                        }
                        push = false;
                    } else {
                        prev = nil;
                    }

                } while (prev != nil);

                curblock = blocks.top();
            }
            break;
        case Pyc::JUMP_FORWARD_A:
        case Pyc::INSTRUMENTED_JUMP_FORWARD_A:
            {
                // Absolute target for every version (older code compared relative operands against positions)
                int offs = ast_relative_jump_target(mod, opcode, operand, pos, false);

                if (mod->verCompare(3, 8) >= 0 && ast_is_while_exit_jump(blocks, offs)) {
                    ast_emit_for_break(blocks, curblock, stack, stack_hist, curpos);
                    break;
                }

                /* Python 3.12+ compiles `break` as a forward jump to just past
                   the loop's END_FOR / POP_TOP cleanup.  The jump can occur
                   before the rest of the loop body, so validate the cleanup
                   trailer at the loop end rather than requiring the entire
                   skipped interval to contain cleanup only. */
                if (mod->verCompare(3, 8) >= 0 && mod->verCompare(3, 12) < 0
                        && ast_is_for_exit_jump(blocks, curpos, offs, code, mod, forElse)) {
                    if (forElse)
                        forElseEnd[ast_innermost_for(blocks).cast<ASTIterBlock>()->start()] = forElse;
                    ast_emit_for_break(blocks, curblock, stack, stack_hist, curpos);
                    break;
                }
                if (mod->verCompare(3, 12) >= 0) {
                    PycRef<ASTBlock> loop;
                    std::stack<PycRef<ASTBlock> > pending = blocks;
                    while (!pending.empty()) {
                        ASTBlock::BlkType bt = pending.top()->blktype();
                        if (bt == ASTBlock::BLK_FOR
                                || bt == ASTBlock::BLK_ASYNCFOR) {
                            loop = pending.top();
                            break;
                        }
                        pending.pop();
                    }
                    bool sawEndFor = false;
                    int forElseStart = -1;
                    bool cleanupOnly = loop != NULL && curpos < loop->end()
                            && loop->end() < offs;
                    int scanPos = cleanupOnly ? loop->end() : offs;
                    while (cleanupOnly && scanPos < offs) {
                        int scanOp = 0, scanArg = 0, scanAfter = 0;
                        if (!ast_read_wordcode_instr(code->code(), mod, scanPos,
                                scanOp, scanArg, scanAfter)
                                || scanAfter <= scanPos || scanAfter > offs) {
                            cleanupOnly = false;
                            break;
                        }
                        if (scanOp != Pyc::CACHE && scanOp != Pyc::END_FOR
                                && scanOp != Pyc::INSTRUMENTED_END_FOR_A
                                && scanOp != Pyc::POP_TOP && scanOp != Pyc::POP_ITER
                                && scanOp != Pyc::INSTRUMENTED_POP_ITER_A) {
                            // Code between the loop cleanup and the break target is the for-else body
                            if (sawEndFor && !(scanOp == Pyc::JUMP_FORWARD_A
                                    && ast_relative_jump_target(mod, scanOp, scanArg, scanAfter, false) == offs)) {
                                forElseStart = scanPos;
                                scanPos = offs;
                            } else {
                                cleanupOnly = false;
                            }
                            break;
                        }
                        if (scanOp == Pyc::END_FOR
                                || scanOp == Pyc::INSTRUMENTED_END_FOR_A)
                            sawEndFor = true;
                        scanPos = scanAfter;
                    }
                    if (loop != NULL && cleanupOnly && sawEndFor
                            && scanPos == offs) {
                        if (forElseStart > 0)
                            forElseEnd[loop.cast<ASTIterBlock>()->start()] = offs;
                        PycRef<ASTNode> breakNode =
                                new ASTKeyword(ASTKeyword::KW_BREAK);
                        PycRef<ASTBlock> breakDest = curblock;
                        /* Exception-table handlers can be decoded out of
                           line and reattached before this success jump is
                           visited.  In that case the current loop already
                           ends with a complete try/except container; the
                           source break belongs to its try body. */
                        for (auto outer = loop->nodes().rbegin();
                                outer != loop->nodes().rend();
                                ++outer) {
                            if ((*outer).type() != ASTNode::NODE_BLOCK
                                    || (*outer).cast<ASTBlock>()->blktype()
                                        != ASTBlock::BLK_CONTAINER)
                                continue;
                            PycRef<ASTBlock> container =
                                    (*outer).cast<ASTBlock>();
                            for (const auto& child : container->nodes()) {
                                if (child.type() == ASTNode::NODE_BLOCK
                                        && child.cast<ASTBlock>()->blktype()
                                            == ASTBlock::BLK_TRY) {
                                    breakDest = child.cast<ASTBlock>();
                                    break;
                                }
                            }
                            if (breakDest != curblock)
                                break;
                        }
                        /* A second iterator-cleanup POP_TOP can precede the
                           jump itself.  It has already been decoded by this
                           point, so remove it only when it is the loop's exact
                           iterator node at the end of the loop body. */
                        if (!loop->nodes().empty()
                                && (loop->nodes().back() ==
                                        loop.cast<ASTIterBlock>()->iter()
                                    || sameName(loop->nodes().back(),
                                        loop.cast<ASTIterBlock>()->iter())))
                            loop->removeLast();
                        if (breakDest != loop && !breakDest->nodes().empty()
                                && (breakDest->nodes().back() ==
                                        loop.cast<ASTIterBlock>()->iter()
                                    || sameName(breakDest->nodes().back(),
                                        loop.cast<ASTIterBlock>()->iter())))
                            breakDest->removeLast();
                        breakDest->append(breakNode);
                        // Only an iterator-cleanup POP_TOP directly after the jump belongs to the break
                        int nextOp = 0, nextArg = 0, nextAt = pos, after = 0;
                        while (ast_read_wordcode_instr(code->code(), mod, nextAt, nextOp, nextArg, after)
                                && nextOp == Pyc::CACHE)
                            nextAt = after;
                        skipNextPopTop = nextOp == Pyc::POP_TOP;
                        break;
                    }
                }

                // 3.11+ try exit jumping over the handlers of a deferred (already closed) try: nothing else ends here
                {
                    auto pendingTry = deferredExceptContainers.find(ast_next_instr_offset_after_caches(mod, opcode, pos));
                    if (mod->verCompare(3, 11) >= 0 && pendingTry != deferredExceptContainers.end()
                            && offs > pos) {
                        pendingTry->second->setEnd(offs);
                        break;
                    }
                }
                /* Chained-comparison trailer: the JUMP_FORWARD that jumps over
                   the trampoline straight to the body. Skip it (and the
                   trampoline) without treating it as an if/else boundary. */
                if (chainSkipJumps.count(curpos)) {
                    int tgt = chainSkipJumps[curpos];
                    while (pos < tgt && !source.atEof()) {
                        curpos = pos;
                        bc_next(source, mod, opcode, operand, pos);
                    }
                    continue;
                }

                if (curblock->blktype() == ASTBlock::BLK_CONTAINER) {
                    PycRef<ASTContainerBlock> cont = curblock.cast<ASTContainerBlock>();
                    if (cont->hasExcept()) {
                        if (mod->verCompare(3, 11) >= 0
                                && offs < cont->except() && blocks.size() > 1) {
                            /* This is an enclosing if's failure branch, not the
                               normal jump over the exception handler. Keep the
                               completed try aside until its real handler and
                               continue decoding the jump against the if. */
                            blocks.pop();
                            curblock = blocks.top();
                            curblock->append(cont.cast<ASTNode>());
                            deferredExceptContainers[cont->except()] = cont;
                        } else {
                            stack_hist.push(stack);

                            curblock->setEnd(offs);
                            PycRef<ASTBlock> except = new ASTCondBlock(
                                    ASTBlock::BLK_EXCEPT, offs, NULL, false);
                            except->init();
                            blocks.push(except);
                            curblock = blocks.top();
                            break;
                        }
                    } else {
                        break;
                    }
                }

                if (!stack_hist.empty()) {
                    if (stack.empty()) // if it's part of if-expression, TOS at the moment is the result of "if" part
                        stack = stack_hist.top();
                    stack_hist.pop();
                }

                PycRef<ASTBlock> prev = curblock;
                PycRef<ASTBlock> nil;
                bool push = true;

                do {
                    blocks.pop();

                    if (!blocks.empty())
                        blocks.top()->append(prev.cast<ASTNode>());

                    if (prev->blktype() == ASTBlock::BLK_IF
                            || prev->blktype() == ASTBlock::BLK_ELIF) {
                        if (offs == pos) {
                            prev = nil;
                            continue;
                        }

                        if (push) {
                            stack_hist.push(stack);
                        }
                        PycRef<ASTBlock> next = new ASTBlock(ASTBlock::BLK_ELSE, offs);
                        if (prev->inited() == ASTCondBlock::PRE_POPPED) {
                            next->init(ASTCondBlock::PRE_POPPED);
                        }

                        blocks.push(next.cast<ASTBlock>());
                        prev = nil;
                    } else if (prev->blktype() == ASTBlock::BLK_EXCEPT) {
                        if (offs == pos) {
                            prev = nil;
                            continue;
                        }
                        // 3.11+: a clause whose no-match target is the final RERAISE has no following clause
                        bool lastClause = false;
                        if (mod->verCompare(3, 11) >= 0 && prev->end() >= pos) {
                            int nextOp = 0, nextArg = 0, nextAt = prev->end(), afterNext = 0;
                            while (ast_read_wordcode_instr(code->code(), mod, nextAt, nextOp, nextArg, afterNext)
                                    && nextOp == Pyc::CACHE)
                                nextAt = afterNext;
                            lastClause = nextOp == Pyc::RERAISE || nextOp == Pyc::RERAISE_A;
                        }
                        // A bare `except:` is always the last clause
                        if (mod->verCompare(3, 11) >= 0 && prev.cast<ASTCondBlock>()->cond() == nullptr)
                            lastClause = true;

                        if (push) {
                            stack_hist.push(stack);
                        }
                        PycRef<ASTBlock> next = new ASTCondBlock(ASTBlock::BLK_EXCEPT, offs, NULL, false);
                        next->init();
                        // Provisional clause: dropped by the printer if it never receives code
                        if (lastClause)
                            next->setProcessed();

                        blocks.push(next.cast<ASTBlock>());
                        prev = nil;
                    } else if (prev->blktype() == ASTBlock::BLK_ELSE) {
                        /* Special case */
                        prev = blocks.top();
                        if (!push) {
                            stack = stack_hist.top();
                            stack_hist.pop();
                        }
                        push = false;

                        if (prev->blktype() == ASTBlock::BLK_MAIN) {
                            /* Something went out of control! */
                            prev = nil;
                        }
                    } else if (prev->blktype() == ASTBlock::BLK_TRY
                            && prev->end() < offs) {
                        /* Need to add an except/finally block */
                        if (!stack_hist.empty()) {
                            stack = stack_hist.top();
                            stack_hist.pop();
                        }

                        if (blocks.top()->blktype() == ASTBlock::BLK_CONTAINER) {
                            PycRef<ASTContainerBlock> cont = blocks.top().cast<ASTContainerBlock>();
                            if (cont->hasExcept()) {
                                if (push) {
                                    stack_hist.push(stack);
                                }

                                PycRef<ASTBlock> except = new ASTCondBlock(ASTBlock::BLK_EXCEPT, offs, NULL, false);
                                except->init();
                                blocks.push(except);
                            }
                        } else {
                            /* Best-effort fallback for newer bytecode stack shapes. */
                        }
                        prev = nil;
                    } else {
                        prev = nil;
                    }

                } while (prev != nil);

                if (!blocks.empty()) {
                    curblock = blocks.top();
                    if (curblock->blktype() == ASTBlock::BLK_EXCEPT)
                        curblock->setEnd(offs);
                }
            }
            break;
        case Pyc::BUILD_TUPLE_UNPACK_A:
        case Pyc::BUILD_TUPLE_UNPACK_WITH_CALL_A:
        case Pyc::BUILD_LIST_UNPACK_A:
            {
                // 3.5-3.8 starred displays and *args: concatenate operand iterables
                std::vector<PycRef<ASTNode> > parts(operand);
                for (int i = operand - 1; i >= 0; --i) {
                    parts[i] = stack.top();
                    stack.pop();
                }
                std::vector<PycRef<ASTNode> > values;
                for (const auto& part : parts)
                    ast_append_unpacked(values, part);
                if (opcode == Pyc::BUILD_LIST_UNPACK_A)
                    stack.push(new ASTList(ASTList::value_t(values.begin(), values.end())));
                else
                    stack.push(new ASTTuple(ASTTuple::value_t(values.begin(), values.end())));
            }
            break;
        case Pyc::BUILD_SET_UNPACK_A:
            {
                // 3.5-3.8 {*a, *b}: concatenate operand iterables into a set display
                std::vector<PycRef<ASTNode> > parts(operand);
                for (int i = operand - 1; i >= 0; --i) {
                    parts[i] = stack.top();
                    stack.pop();
                }
                ASTSet::value_t values;
                for (const auto& part : parts) {
                    if (part.type() == ASTNode::NODE_SET) {
                        for (const auto& v : part.cast<ASTSet>()->values())
                            values.push_back(v);
                    } else {
                        std::vector<PycRef<ASTNode> > items;
                        ast_append_unpacked(items, part);
                        values.insert(values.end(), items.begin(), items.end());
                    }
                }
                stack.push(new ASTSet(values));
            }
            break;
        case Pyc::BUILD_MAP_UNPACK_A:
        case Pyc::BUILD_MAP_UNPACK_WITH_CALL_A:
            {
                // 3.5-3.8 {**a, **b} and **kwargs: merge operand mappings (3.5 WITH_CALL packs fnloc in the high byte)
                int count = mod->verCompare(3, 6) < 0 ? (operand & 0xFF) : operand;
                std::vector<PycRef<ASTNode> > parts(count);
                for (int i = count - 1; i >= 0; --i) {
                    parts[i] = stack.top();
                    stack.pop();
                }
                PycRef<ASTMap> map = new ASTMap();
                for (const auto& part : parts)
                    ast_merge_mapping(map, part);
                stack.push(map.cast<ASTNode>());
            }
            break;
        case Pyc::LIST_TO_TUPLE:
            {
                /* Python 3.9+: convert the list at TOS into a tuple
                   (used when building *args for calls). */
                PycRef<ASTNode> list = stack.top();
                stack.pop();
                if (list.type() == ASTNode::NODE_LIST) {
                    const auto& lv = list.cast<ASTList>()->values();
                    ASTTuple::value_t tv(lv.begin(), lv.end());
                    stack.push(new ASTTuple(tv));
                } else {
                    stack.push(list);
                }
            }
            break;
        case Pyc::RETURN_GENERATOR:
            /* Python 3.11 generator/coroutine prologue; the pushed generator
               object is immediately discarded by a following POP_TOP. */
            stack.push(nullptr);
            break;
        case Pyc::LIST_APPEND:
        case Pyc::LIST_APPEND_A:
            {
                PycRef<ASTNode> value = stack.top();
                stack.pop();

                PycRef<ASTNode> list = stack.top();

                // Depth-1 append onto a list display builds [a, *x, b] or *args (comprehensions append at depth >= 2)
                if (opcode == Pyc::LIST_APPEND_A && operand == 1 && list.type() == ASTNode::NODE_LIST) {
                    ASTList::value_t values = list.cast<ASTList>()->values();
                    values.push_back(value);
                    stack.pop();
                    stack.push(new ASTList(values));
                    break;
                }
                if ((curblock->blktype() == ASTBlock::BLK_FOR
                            || curblock->blktype() == ASTBlock::BLK_ASYNCFOR)
                        && curblock.cast<ASTIterBlock>()->isComprehension()) {
                    stack.pop();
                    stack.push(new ASTComprehension(value));
                } else {
                    const char* cn = code->name() != NULL ? code->name()->value() : NULL;
                    if (curblock->blktype() == ASTBlock::BLK_ASYNCFOR) {
                        fprintf(stderr, "Warning: async comprehension in %s could not be reconstructed (offset %d)\n",
                                code->name() != nullptr ? code->name()->value() : "<unknown>", curpos);
                        cleanBuild = false;
                        stack.push(new ASTSubscr(list, value));
                    } else if (cn && !strcmp(cn, "<listcomp>")) {
                        /* Filtered list comprehension: the append is inside the
                           filter block, so record the value as a yield-style
                           marker and let SynthGenexpr rebuild the comprehension
                           (with its filter condition). */
                        curblock->append(new ASTReturn(value, ASTReturn::YIELD));
                    } else {
                        stack.push(new ASTSubscr(list, value)); /* Total hack */
                    }
                }
            }
            break;
        case Pyc::SET_UPDATE_A:
            {
                PycRef<ASTNode> rhs = stack.top();
                stack.pop();
                PycRef<ASTSet> lhs = stack.top().try_cast<ASTSet>();
                stack.pop();

                ASTSet::value_t result;
                if (lhs != nullptr)
                    result = lhs->values();
                else
                    cleanBuild = false;
                PycRef<PycObject> obj = rhs.type() == ASTNode::NODE_OBJECT
                        ? rhs.cast<ASTObject>()->object() : PycRef<PycObject>();
                if (obj != nullptr && obj->type() == PycObject::TYPE_FROZENSET) {
                    for (const auto& it : obj.cast<PycSet>()->values())
                        result.push_back(new ASTObject(it));
                } else {
                    // Any other iterable is a starred element ({*x, 1})
                    result.push_back(new ASTUnary(rhs, ASTUnary::UN_STAR));
                }

                stack.push(new ASTSet(result));
            }
            break;
        case Pyc::LIST_EXTEND_A:
            {
                PycRef<ASTNode> rhs = stack.top();
                stack.pop();
                PycRef<ASTList> lhs = stack.top().try_cast<ASTList>();
                stack.pop();

                ASTList::value_t result;
                if (lhs != nullptr)
                    result = lhs->values();
                else
                    cleanBuild = false;
                // Const tuples expand in place; any other iterable is a starred element ([a, *x])
                std::vector<PycRef<ASTNode> > items;
                if (rhs.type() == ASTNode::NODE_OBJECT)
                    ast_append_unpacked(items, rhs);
                else
                    items.push_back(new ASTUnary(rhs, ASTUnary::UN_STAR));
                result.insert(result.end(), items.begin(), items.end());

                stack.push(new ASTList(result));
            }
            break;
        case Pyc::LOAD_ATTR_A:
            {
                PycRef<ASTNode> name = stack.top();
                // Python 2 `import a.b as c` walks submodules with LOAD_ATTR
                if (name.type() == ASTNode::NODE_IMPORT)
                    name.cast<ASTImport>()->setModuleAlias(true);
                if (name.type() != ASTNode::NODE_IMPORT) {
                    stack.pop();

                    if (mod->verCompare(3, 12) >= 0) {
                        if (operand & 1) {
                            /* Changed in version 3.12:
                            If the low bit of name is set, then a NULL or self is pushed to the stack
                            before the attribute or unbound method respectively. */
                            stack.push(nullptr);
                        }
                        operand >>= 1;
                    }

                    stack.push(new ASTBinary(name, new ASTName(code->getName(operand)), ASTBinary::BIN_ATTR));
                }
            }
            break;
        case Pyc::LOAD_SUPER_ATTR_A:
        case Pyc::INSTRUMENTED_LOAD_SUPER_ATTR_A:
            {
                // 3.12+ super(): bit 0 = method load (NULL|self slot), bit 1 = two-arg super(cls, self)
                PycRef<ASTNode> self = stack.top();
                stack.pop();
                PycRef<ASTNode> cls = stack.top();
                stack.pop();
                PycRef<ASTNode> superFunc = stack.top();
                stack.pop();
                ASTCall::pparam_t superArgs;
                if (operand & 2) {
                    superArgs.push_back(cls);
                    superArgs.push_back(self);
                }
                PycRef<ASTNode> superCall = new ASTCall(superFunc, superArgs,
                                                        ASTCall::kwparam_t());
                if (operand & 1)
                    stack.push(nullptr);
                stack.push(new ASTBinary(superCall, new ASTName(code->getName(operand >> 2)),
                                         ASTBinary::BIN_ATTR));
            }
            break;
        case Pyc::LOAD_ASSERTION_ERROR:
            {
                PycRef<PycString> assertName = new PycString();
                assertName->setValue("AssertionError");
                stack.push(new ASTName(assertName));
            }
            break;
        case Pyc::LOAD_BUILD_CLASS:
            stack.push(new ASTLoadBuildClass(new PycObject()));
            break;
        case Pyc::LOAD_CLOSURE_A:
            // Closure cells are collected by BUILD_TUPLE and consumed by MAKE_FUNCTION/MAKE_CLOSURE; keep the stack balanced
            stack.push(new ASTName(code->getCellVar(mod, operand)));
            break;
        case Pyc::MAKE_CELL_A:
        case Pyc::COPY_FREE_VARS_A:
            /* Python 3.11 function prologue; no stack effect for decompilation */
            break;
        case Pyc::LOAD_CONST_A:
            {
                PycRef<ASTObject> t_ob = new ASTObject(code->getConst(operand));

                if ((t_ob->object().type() == PycObject::TYPE_TUPLE ||
                        t_ob->object().type() == PycObject::TYPE_SMALL_TUPLE) &&
                        !t_ob->object().cast<PycTuple>()->values().size()) {
                    ASTTuple::value_t values;
                    stack.push(new ASTTuple(values));
                } else if (t_ob->object().type() == PycObject::TYPE_NONE) {
                    stack.push(NULL);
                } else {
                    stack.push(t_ob.cast<ASTNode>());
                }
            }
            break;
        case Pyc::LOAD_DEREF_A:
        case Pyc::LOAD_CLASSDEREF_A:
            stack.push(new ASTName(code->getCellVar(mod, operand)));
            break;
        case Pyc::LOAD_FAST_A:
        case Pyc::LOAD_FAST_BORROW_A:
        case Pyc::LOAD_FAST_AND_CLEAR_A:
        case Pyc::LOAD_FAST_CHECK_A:
            if (mod->verCompare(1, 3) < 0)
                stack.push(new ASTName(code->getName(operand)));
            else
                stack.push(new ASTName(code->getLocal(operand)));
            break;
        case Pyc::LOAD_FAST_LOAD_FAST_A:
        case Pyc::LOAD_FAST_BORROW_LOAD_FAST_BORROW_A:
            stack.push(new ASTName(code->getLocal(operand >> 4)));
            stack.push(new ASTName(code->getLocal(operand & 0xF)));
            break;
        case Pyc::LOAD_GLOBAL_A:
            if (mod->verCompare(3, 11) >= 0) {
                // Loads the global named co_names[namei>>1] onto the stack.
                if (operand & 1) {
                    /* Changed in version 3.11: 
                    If the low bit of "NAMEI" (operand) is set, 
                    then a NULL is pushed to the stack before the global variable. */
                    stack.push(nullptr);
                }
                operand >>= 1;
            }
            stack.push(new ASTName(code->getName(operand)));
            break;
        case Pyc::LOAD_LOCALS:
            stack.push(new ASTNode(ASTNode::NODE_LOCALS));
            break;
        case Pyc::LOAD_SMALL_INT_A:
            stack.push(new ASTObject(new PycInt(operand)));
            break;
        case Pyc::LOAD_COMMON_CONSTANT_A:
            {
                static const char *common_constants[] = {
                    "AssertionError", "NotImplementedError", "tuple", "all", "any",
                    "list", "set",
                };
                if (operand >= 0 && operand < 7) {
                    PycRef<PycString> name = new PycString(PycObject::TYPE_STRING);
                    name->setValue(common_constants[operand]);
                    stack.push(new ASTName(name));
                } else if (operand == 7) {
                    stack.push(new ASTObject(Pyc_None));
                } else if (operand == 8) {
                    // The empty str, not bytes (TYPE_STRING prints as b'' on Python 3)
                    PycRef<PycObject> value = new PycString(PycObject::TYPE_UNICODE);
                    value.cast<PycString>()->setValue("");
                    stack.push(new ASTObject(value));
                } else if (operand == 9) {
                    stack.push(new ASTObject(Pyc_True));
                } else if (operand == 10) {
                    stack.push(new ASTObject(Pyc_False));
                } else if (operand == 11) {
                    stack.push(new ASTObject(new PycInt(-1)));
                } else {
                    PycRef<PycString> name = new PycString(PycObject::TYPE_STRING);
                    name->setValue("<LOAD_COMMON_CONSTANT>");
                    stack.push(new ASTName(name));
                }
            }
            break;
        case Pyc::STORE_LOCALS:
            stack.pop();
            break;
        case Pyc::LOAD_METHOD_A:
            {
                // Behave like LOAD_ATTR
                PycRef<ASTNode> name = stack.top();
                stack.pop();
                stack.push(new ASTBinary(name, new ASTName(code->getName(operand)), ASTBinary::BIN_ATTR));
            }
            break;
        case Pyc::LOAD_SPECIAL_A:
            {
                static const char *special_methods[] = {
                    "__enter__", "__exit__", "__aenter__", "__aexit__",
                };
                PycRef<ASTNode> owner = stack.top();
                stack.pop();
                /* Python 3.14 lowers `with` to LOAD_SPECIAL(__enter__) /
                   LOAD_SPECIAL(__exit__) instead of BEFORE_WITH.  The
                   pre-pass has already validated its exception-table shape. */
                auto withStart = withBodyEndByBefore.find(curpos);
                if (withStart != withBodyEndByBefore.end()) {
                    PycRef<ASTBlock> withblock = new ASTWithBlock(withStart->second);
                    blocks.push(withblock);
                    curblock = blocks.top();
                }
                PycRef<PycString> attr = new PycString(PycObject::TYPE_STRING);
                if (operand >= 0 && operand < 4) {
                    attr->setValue(special_methods[operand]);
                } else {
                    char name[32];
                    snprintf(name, sizeof(name), "__special_%d__", operand);
                    attr->setValue(name);
                }
                stack.push(nullptr);
                stack.push(new ASTBinary(owner, new ASTName(attr), ASTBinary::BIN_ATTR));
            }
            break;
        case Pyc::LOAD_NAME_A:
            stack.push(new ASTName(code->getName(operand)));
            break;
        case Pyc::MAKE_CLOSURE_A:
        case Pyc::MAKE_FUNCTION_A:
            {
                PycRef<ASTNode> fun_code = stack.top();
                stack.pop();

                /* Test for the qualified name of the function (at TOS) */
                int tos_type = fun_code.cast<ASTObject>()->object().type();
                if (tos_type != PycObject::TYPE_CODE &&
                    tos_type != PycObject::TYPE_CODE2) {
                    fun_code = stack.top();
                    stack.pop();
                }

                ASTFunction::defarg_t defArgs, kwDefArgs;

                if (mod->verCompare(3, 6) >= 0) {
                    /* Python 3.6+: the operand is a flag bitmask, and each set
                       flag has a single object pushed on the stack (bottom to
                       top): 0x01 defaults tuple, 0x02 kwonly-defaults dict,
                       0x04 annotations, 0x08 closure tuple. The code object was
                       already popped above. They must be consumed top-down. */
                    if (operand & 0x08) {
                        /* closure: tuple of cells - not needed for source */
                        stack.pop();
                    }
                    if (operand & 0x04) {
                        /* annotations - not reconstructed here */
                        stack.pop();
                    }
                    if (operand & 0x02) {
                        /* keyword-only defaults: a mapping on the stack */
                        PycRef<ASTNode> kwd = stack.top();
                        stack.pop();
                        if (kwd != NULL && kwd.type() == ASTNode::NODE_MAP) {
                            for (const auto& it : kwd.cast<ASTMap>()->values())
                                kwDefArgs.push_back(it.second);
                        } else if (kwd != NULL && kwd.type() == ASTNode::NODE_CONST_MAP) {
                            for (const auto& v : kwd.cast<ASTConstMap>()->values())
                                kwDefArgs.push_back(v);
                        }
                    }
                    if (operand & 0x01) {
                        /* positional defaults: a tuple on the stack */
                        PycRef<ASTNode> defs = stack.top();
                        stack.pop();
                        if (defs != NULL && defs.type() == ASTNode::NODE_TUPLE) {
                            for (const auto& v : defs.cast<ASTTuple>()->values())
                                defArgs.push_back(v);
                        } else if (defs != NULL && defs.type() == ASTNode::NODE_OBJECT) {
                            PycRef<PycObject> o = defs.cast<ASTObject>()->object();
                            if (o->type() == PycObject::TYPE_TUPLE
                                    || o->type() == PycObject::TYPE_SMALL_TUPLE) {
                                for (const auto& it : o.cast<PycTuple>()->values())
                                    defArgs.push_back(new ASTObject(it));
                            }
                        }
                    }
                } else {
                    // Pre-3.6 MAKE_CLOSURE: the closure cell tuple sits right under the code object
                    if (opcode == Pyc::MAKE_CLOSURE_A)
                        stack.pop();
                    const int defCount = operand & 0xFF;
                    const int kwDefCount = (operand >> 8) & 0xFF;
                    for (int i = 0; i < defCount; ++i) {
                        defArgs.push_front(stack.top());
                        stack.pop();
                    }
                    for (int i = 0; i < kwDefCount; ++i) {
                        kwDefArgs.push_front(stack.top());
                        stack.pop();
                    }
                }
                stack.push(new ASTFunction(fun_code, defArgs, kwDefArgs));
            }
            break;
        case Pyc::MAKE_FUNCTION:
            {
                PycRef<ASTNode> fun_code = stack.top();
                stack.pop();
                stack.push(new ASTFunction(fun_code, {}, {}));
            }
            break;
        case Pyc::SET_FUNCTION_ATTRIBUTE_A:
            {
                PycRef<ASTNode> fun = stack.top();
                stack.pop();
                if (fun != nullptr && fun.type() == ASTNode::NODE_FUNCTION) {
                    PycRef<ASTNode> attribute;
                    if (!stack.empty()) {
                        attribute = stack.top();
                        stack.pop();
                    }
                    if (operand == 0x01 && attribute != nullptr) {
                        ASTFunction::defarg_t defArgs;
                        if (attribute.type() == ASTNode::NODE_TUPLE) {
                            for (const auto& value : attribute.cast<ASTTuple>()->values())
                                defArgs.push_back(value);
                        } else if (attribute.type() == ASTNode::NODE_OBJECT) {
                            PycRef<PycObject> object =
                                    attribute.cast<ASTObject>()->object();
                            if (object->type() == PycObject::TYPE_TUPLE
                                    || object->type() == PycObject::TYPE_SMALL_TUPLE) {
                                for (const auto& value : object.cast<PycTuple>()->values())
                                    defArgs.push_back(new ASTObject(value));
                            }
                        }
                        fun.cast<ASTFunction>()->setDefargs(std::move(defArgs));
                    }
                    stack.push(fun);
                } else if (!stack.empty()) {
                    PycRef<ASTNode> maybe_fun = stack.top();
                    stack.pop();
                    if (maybe_fun != nullptr && maybe_fun.type() == ASTNode::NODE_FUNCTION)
                        stack.push(maybe_fun);
                    else {
                        cleanBuild = false;
                        stack.push(fun);
                    }
                } else {
                    cleanBuild = false;
                    stack.push(fun);
                }
            }
            break;
        case Pyc::BEGIN_FINALLY:
        case Pyc::CALL_FINALLY_A:
        case Pyc::POP_FINALLY_A:
            // 3.8 finally bookkeeping (runtime markers with no source form)
        case Pyc::NOP:
        case Pyc::NOT_TAKEN:
        case Pyc::INSTRUMENTED_NOT_TAKEN_A:
        case Pyc::TO_BOOL:
            break;
        case Pyc::END_ASYNC_FOR:
        case Pyc::END_ASYNC_FOR_A:
        case Pyc::INSTRUMENTED_END_ASYNC_FOR_A:
            // Only the async-for terminator closes the loop; NOT_TAKEN sits between END_SEND and the store
            if (mod->verCompare(3, 11) >= 0 && curblock->blktype() == ASTBlock::BLK_ASYNCFOR && blocks.size() > 1) {
                PycRef<ASTIterBlock> loop = curblock.cast<ASTIterBlock>();
                PycRef<ASTNode> idx = loop->index();
                if (!loop->inited() || idx == nullptr || idx.type() == ASTNode::NODE_OBJECT) {
                    fprintf(stderr, "Warning: async for in %s could not be reconstructed (offset %d)\n",
                            code->name() != nullptr ? code->name()->value() : "<unknown>", curpos);
                    cleanBuild = false;
                }
                blocks.pop();
                curblock = blocks.top();
                curblock->append(loop.cast<ASTNode>());
                break;
            }
            // 3.11+ already closed the loop at its back-edge; this opcode is only the terminator
            if (mod->verCompare(3, 11) >= 0)
                break;
            if (opcode == Pyc::END_ASYNC_FOR) {
                fprintf(stderr, "Unsupported opcode: %s (%d), emitting placeholder\n",
                        Pyc::OpcodeName(opcode), opcode);
                cleanBuild = false;
                curblock->append(new ASTUnsupported(std::string("# unsupported opcode ") +
                                 Pyc::OpcodeName(opcode)));
            }
            break;
        case Pyc::POP_ITER:
        case Pyc::INSTRUMENTED_POP_ITER_A:
            // 3.14 inline comprehension exit: same cleanup slot as 3.13's POP_TOP
            if (inlineCompActive && inlineCompCleanupOps > 0) {
                inlineCompCleanupOps--;
                break;
            }
            if (!stack.empty())
                stack.pop();
            break;
        case Pyc::POP_BLOCK:
            {
                // 3.10 break in a try: POP_BLOCK then a jump to the while exit, or a copy of that exit
                if (mod->verCompare(3, 10) == 0) {
                    int breakEnd = ast_py310_while_break_end(code, mod, blocks, exceptAsSkip, pos);
                    if (breakEnd > pos) {
                        ast_emit_copied_break(curblock, source, mod, curpos, opcode, operand, pos, breakEnd);
                        break;
                    }
                }
                // Early exit from a try body (POP_BLOCK; continue/break/return): only the exit right before the handler ends the try
                PycRef<ASTBlock> ownerTry;
                {
                    std::stack<PycRef<ASTBlock> > pending = blocks;
                    while (!pending.empty() && (pending.top()->blktype() == ASTBlock::BLK_IF
                                || pending.top()->blktype() == ASTBlock::BLK_ELIF
                                || pending.top()->blktype() == ASTBlock::BLK_ELSE))
                        pending.pop();
                    if (!pending.empty() && pending.top()->blktype() == ASTBlock::BLK_TRY)
                        ownerTry = pending.top();
                }
                if (ownerTry != nullptr && ownerTry->end() > pos && mod->verCompare(3, 11) < 0) {
                    // 3.10 copies a short epilogue in front of the handler; it is not a statement between try and except
                    if (mod->verCompare(3, 10) == 0 && code->code() != nullptr) {
                        int tail = ast_py310_exit_block_len(code, mod, pos);
                        int codeLen = code->code()->length();
                        int tailOp = 0, tailArg = 0, tailNext = 0;
                        bool tailRead = ast_read_wordcode_instr(code->code(), mod, pos, tailOp, tailArg, tailNext);
                        // LOAD_CONST; RETURN is the implicit None the 3.10 compiler pastes on every
                        // fall-through, including each except. The peek below already leaves that
                        // return inside its clause. Skipping it splits a second except off the try.
                        if (tailRead && tailOp != Pyc::LOAD_CONST_A
                                && tail >= 4 && pos + tail == ownerTry->end() && pos + tail < codeLen) {
                            const char* bytes = code->code()->value();
                            bool again = false;
                            for (int i = pos + tail; i + tail <= codeLen; i += 2) {
                                if (memcmp(bytes + pos, bytes + i, tail) == 0) {
                                    again = true;
                                    break;
                                }
                            }
                            if (again) {
                                if (py310SharedEpilogue.empty())
                                    py310SharedEpilogue.assign(bytes + pos, bytes + pos + tail);
                                int skipTo = pos + tail;
                                while (pos < skipTo && !source.atEof()) {
                                    curpos = pos;
                                    bc_next(source, mod, opcode, operand, pos);
                                }
                                break;
                            }
                        }
                    }
                    // `else: return ...` sits between POP_BLOCK and the handler and does not match the while exit.
                    // A copy of the same bytes later is the implicit return pasted on every clause, not an else.
                    if (mod->verCompare(3, 10) == 0 && code->code() != nullptr && curblock == ownerTry) {
                        int tail = ast_py310_exit_block_len(code, mod, pos);
                        int codeLen = code->code()->length();
                        int firstOp = 0, firstArg = 0, firstNext = 0;
                        bool firstRead = ast_read_wordcode_instr(code->code(), mod, pos, firstOp, firstArg, firstNext);
                        // None is the implicit fall-through return. Another const belongs inside the try
                        // when its index was interned before the handler's return const.
                        // Basis: CPython appends a new co_const when it is first emitted, and the
                        // handler return is emitted before `else: return <new>`. A greater index is
                        // that else. A const already used earlier keeps a smaller index. An equal
                        // index is the same object as the handler return, so it is not else.
                        bool constInsideTry = false;
                        if (firstRead && firstOp == Pyc::LOAD_CONST_A) {
                            PycRef<PycObject> folded = code->getConst(firstArg);
                            constInsideTry = folded != nullptr && folded->type() == PycObject::TYPE_NONE;
                            if (!constInsideTry) {
                                int handlerConst = -1;
                                int hop = 0, harg = 0, hnext = 0, hat = ownerTry->end(), steps = 0;
                                while (steps < 16 && hat < codeLen
                                        && ast_read_wordcode_instr(code->code(), mod, hat, hop, harg, hnext)) {
                                    if (hop == Pyc::LOAD_CONST_A)
                                        handlerConst = harg;
                                    hat = hnext;
                                    steps++;
                                    if (hop == Pyc::RETURN_VALUE || hop == Pyc::RETURN_CONST_A)
                                        break;
                                }
                                constInsideTry = !(handlerConst >= 0 && firstArg > handlerConst);
                            }
                        }
                        if (firstRead && !constInsideTry
                                && tail >= 4 && pos + tail == ownerTry->end() && pos + tail < codeLen) {
                            int lastOp = 0, lastArg = 0, lastNext = 0, scan = pos;
                            while (scan < pos + tail
                                    && ast_read_wordcode_instr(code->code(), mod, scan, lastOp, lastArg, lastNext))
                                scan = lastNext;
                            const char* bytes = code->code()->value();
                            bool again = false;
                            for (int i = pos + tail; i + tail <= codeLen; i += 2) {
                                if (memcmp(bytes + pos, bytes + i, tail) == 0) {
                                    again = true;
                                    break;
                                }
                            }
                            if (!again && (lastOp == Pyc::RETURN_VALUE || lastOp == Pyc::RETURN_CONST_A)
                                    && blocks.size() > 1) {
                                if (!stack_hist.empty()) {
                                    stack = stack_hist.top();
                                    stack_hist.pop();
                                }
                                blocks.pop();
                                curblock = blocks.top();
                                curblock->append(ownerTry.cast<ASTNode>());
                                stack_hist.push(stack);
                                PycRef<ASTBlock> elseblk = new ASTBlock(ASTBlock::BLK_ELSE, ownerTry->end());
                                elseblk->init();
                                blocks.push(elseblk);
                                curblock = blocks.top();
                                py310InlinedElseHandlers.insert(ownerTry->end());
                                break;
                            }
                        }
                    }
                    PycBuffer peek(code->code()->value(), code->code()->length());
                    int nextOp = 0, nextArg = 0, afterNext = pos;
                    if (peek.setPos(pos)) {
                        // Skip loop-iterator cleanup and a constant return value before the exit itself
                        int steps = 0;
                        do {
                            bc_next(peek, mod, nextOp, nextArg, afterNext);
                        } while (++steps < 4 && !peek.atEof()
                                 && (nextOp == Pyc::POP_TOP || nextOp == Pyc::ROT_TWO
                                     || nextOp == Pyc::ROT_THREE || nextOp == Pyc::LOAD_CONST_A));
                        bool jumpExit = nextOp == Pyc::JUMP_ABSOLUTE_A || nextOp == Pyc::JUMP_FORWARD_A;
                        // A return never closes the try here (3.7 has no POP_BLOCK before it); the handler start does
                        if (nextOp == Pyc::RETURN_VALUE || (jumpExit && afterNext != ownerTry->end()))
                            break;
                    }
                    // Normal end of the try body: ifs still open inside it end here as well
                    while (curblock != ownerTry && blocks.size() > 1
                            && (curblock->blktype() == ASTBlock::BLK_IF
                                || curblock->blktype() == ASTBlock::BLK_ELIF
                                || curblock->blktype() == ASTBlock::BLK_ELSE)) {
                        PycRef<ASTBlock> done = curblock;
                        blocks.pop();
                        curblock = blocks.top();
                        if (!(done->blktype() == ASTBlock::BLK_ELSE && done->nodes().empty()))
                            curblock->append(done.cast<ASTNode>());
                        if (!stack_hist.empty()) {
                            stack = stack_hist.top();
                            stack_hist.pop();
                        }
                    }
                }
                if (curblock->blktype() == ASTBlock::BLK_CONTAINER ||
                        curblock->blktype() == ASTBlock::BLK_FINALLY) {
                    /* These should only be popped by an END_FINALLY */
                    break;
                }

                if (curblock->blktype() == ASTBlock::BLK_WITH) {
                    // This should only be popped by a WITH_CLEANUP
                    break;
                }

                // Only the loop back-edge artifact (continue) is dropped here; a break before POP_BLOCK is real
                // A continue ending a try body (CONTINUE_LOOP before 3.8) precedes the dead POP_BLOCK and is real
                bool keepTryContinue = curblock->blktype() == ASTBlock::BLK_TRY && mod->verCompare(3, 11) < 0
                        && curblock->nodes().size()
                        && curblock->nodes().back().type() == ASTNode::NODE_KEYWORD
                        && curblock->nodes().back().cast<ASTKeyword>()->key() == ASTKeyword::KW_CONTINUE;
                if (curblock->nodes().size() && !keepTryContinue &&
                        curblock->nodes().back().type() == ASTNode::NODE_KEYWORD
                        && curblock->nodes().back().cast<ASTKeyword>()->key() != ASTKeyword::KW_BREAK) {
                    curblock->removeLast();
                }

                if (curblock->blktype() == ASTBlock::BLK_IF
                        || curblock->blktype() == ASTBlock::BLK_ELIF
                        || curblock->blktype() == ASTBlock::BLK_ELSE
                        || curblock->blktype() == ASTBlock::BLK_TRY
                        || curblock->blktype() == ASTBlock::BLK_EXCEPT
                        || curblock->blktype() == ASTBlock::BLK_FINALLY) {
                    if (!stack_hist.empty()) {
                        stack = stack_hist.top();
                        stack_hist.pop();
                    } else {
                        fprintf(stderr, "Warning: Stack history is empty, something wrong might have happened\n");
                    }
                }

                if (blocks.size() <= 1) {
                    cleanBuild = false;
                    break;
                }

                PycRef<ASTBlock> tmp = curblock;
                blocks.pop();

                if (!blocks.empty())
                    curblock = blocks.top();

                if (!(tmp->blktype() == ASTBlock::BLK_ELSE
                        && tmp->nodes().size() == 0)) {
                    curblock->append(tmp.cast<ASTNode>());
                }

                if (tmp->blktype() == ASTBlock::BLK_FOR && tmp->end() >= pos) {
                    stack_hist.push(stack);

                    PycRef<ASTBlock> blkelse = new ASTBlock(ASTBlock::BLK_ELSE, tmp->end());
                    // for-else body starts right after POP_BLOCK; there is no value to pop first
                    blkelse->init();
                    blocks.push(blkelse);
                    curblock = blocks.top();
                }

                if (curblock->blktype() == ASTBlock::BLK_TRY
                        && tmp->blktype() != ASTBlock::BLK_FOR
                        && tmp->blktype() != ASTBlock::BLK_ASYNCFOR
                        && tmp->blktype() != ASTBlock::BLK_WHILE) {
                    stack = stack_hist.top();
                    stack_hist.pop();

                    tmp = curblock;
                    blocks.pop();
                    curblock = blocks.top();

                    if (!(tmp->blktype() == ASTBlock::BLK_ELSE
                            && tmp->nodes().size() == 0)) {
                        curblock->append(tmp.cast<ASTNode>());
                    }
                }

                if (curblock->blktype() == ASTBlock::BLK_CONTAINER) {
                    PycRef<ASTContainerBlock> cont = curblock.cast<ASTContainerBlock>();

                    if (tmp->blktype() == ASTBlock::BLK_ELSE && !cont->hasFinally()) {

                        /* Pop the container */
                        blocks.pop();
                        curblock = blocks.top();
                        curblock->append(cont.cast<ASTNode>());

                    } else if ((tmp->blktype() == ASTBlock::BLK_ELSE && cont->hasFinally())
                            || (tmp->blktype() == ASTBlock::BLK_TRY && !cont->hasExcept())) {

                        /* Add the finally block */
                        stack_hist.push(stack);

                        PycRef<ASTBlock> final = new ASTBlock(ASTBlock::BLK_FINALLY, 0, true);
                        blocks.push(final);
                        curblock = blocks.top();
                    }
                }

                if ((curblock->blktype() == ASTBlock::BLK_FOR || curblock->blktype() == ASTBlock::BLK_ASYNCFOR)
                        && curblock->end() == pos) {
                    blocks.pop();
                    blocks.top()->append(curblock.cast<ASTNode>());
                    curblock = blocks.top();
                }
            }
            break;
        case Pyc::POP_EXCEPT:
            if (mod->verCompare(3, 10) == 0 && !py310SharedEpilogue.empty() && code->code() != nullptr
                    && pos + (int)py310SharedEpilogue.size() <= code->code()->length()
                    && memcmp(code->code()->value() + pos, py310SharedEpilogue.data(),
                            py310SharedEpilogue.size()) == 0) {
                bool inExcept = false;
                {
                    std::stack<PycRef<ASTBlock> > tmp = blocks;
                    while (!tmp.empty()) {
                        int kind = tmp.top()->blktype();
                        if (kind == ASTBlock::BLK_EXCEPT) {
                            inExcept = true;
                            break;
                        }
                        if (kind == ASTBlock::BLK_WHILE || kind == ASTBlock::BLK_FOR
                                || kind == ASTBlock::BLK_ASYNCFOR)
                            break;
                        tmp.pop();
                    }
                }
                if (inExcept && !py310EpilogueEmitted) {
                    while (blocks.size() > 1 && (curblock->blktype() == ASTBlock::BLK_EXCEPT
                            || curblock->blktype() == ASTBlock::BLK_IF
                            || curblock->blktype() == ASTBlock::BLK_ELIF
                            || curblock->blktype() == ASTBlock::BLK_ELSE)) {
                        PycRef<ASTBlock> done = curblock;
                        blocks.pop();
                        curblock = blocks.top();
                        if (!(done->blktype() == ASTBlock::BLK_ELSE && done->nodes().empty()))
                            curblock->append(done.cast<ASTNode>());
                        if (!stack_hist.empty()) {
                            stack = stack_hist.top();
                            stack_hist.pop();
                        }
                    }
                    if (blocks.size() > 1 && curblock->blktype() == ASTBlock::BLK_CONTAINER) {
                        PycRef<ASTBlock> cont = curblock;
                        blocks.pop();
                        curblock = blocks.top();
                        curblock->append(cont.cast<ASTNode>());
                    }
                    py310EpilogueEmitted = true;
                } else if (py310EpilogueEmitted) {
                    int skipTo = pos + (int)py310SharedEpilogue.size();
                    while (pos < skipTo && !source.atEof()) {
                        curpos = pos;
                        bc_next(source, mod, opcode, operand, pos);
                    }
                    break;
                }
            }
            if (mod->verCompare(3, 9) >= 0 && mod->verCompare(3, 11) < 0
                    && py39_except_cleanup_var >= 0) {
                py39_normal_cleanup_step = 1;
            } else if (mod->verCompare(3, 11) >= 0) {
                py311_cleanup_sequences = 2;
            }
            break;
        case Pyc::PUSH_EXC_INFO:
            // 3.11+ finally handler entry (recorded as a negative offset): the finally body follows, nothing to push
            if (finallyCopySkip.count(-curpos))
                break;
            /* Python 3.11+: pushes the live exception. Use a sentinel so the
               `as <var>` binding and CHECK_EXC_MATCH stay balanced; it is
               consumed by the following STORE (binding) or POP_TOP (discard). */
            {
                PycRef<PycString> s = new PycString();
                s->setValue(EXC_SENTINEL);
                stack.push(new ASTName(s));
            }
            break;
        case Pyc::CHECK_EXC_MATCH:
            {
                /* Python 3.11+: compare the exception (left, kept on the stack
                   for a possible `as` binding) against the handler type. */
                PycRef<ASTNode> right = stack.top();
                stack.pop();
                PycRef<ASTNode> left = stack.top();
                stack.push(new ASTCompare(left, right, ASTCompare::CMP_EXCEPTION));
            }
            break;
        case Pyc::END_FOR:
            {
                // Cleanup left by an inlined comp must not eat the END_FOR of a real for still open here
                if (inlineCompActive && inlineCompCleanupOps > 0
                        && !(curblock->blktype() == ASTBlock::BLK_FOR
                             && curblock->end() != 0 && curblock->end() <= pos)) {
                    inlineCompCleanupOps--;
                    break;
                }
                /* A preceding 3.12+ loop back-edge may already have consumed
                   the iterator state. Keep malformed or partially recovered
                   exception-table regions from underflowing the AST stack. */
                if (!stack.empty())
                    stack.pop();

                if (mod->verCompare(3, 12) >= 0) {
                    int nextOp = 0, nextArg = 0, afterNext = 0;
                    bool readNext = false;
                    int nextPos = pos;
                    do {
                        readNext = ast_read_wordcode_instr(code->code(), mod,
                                nextPos, nextOp, nextArg, afterNext);
                        nextPos = afterNext;
                    } while (readNext && nextOp == Pyc::CACHE);
                    if (readNext && nextOp == Pyc::POP_TOP)
                        skipNextPopTop = true;
                }

                if ((opcode == Pyc::END_FOR) && (mod->majorVer() == 3) && (mod->minorVer() == 12)) {
                    // one additional pop for python 3.12
                    if (!stack.empty())
                        stack.pop();
                }

                // end for loop here
                /* TODO : Ensure that FOR loop ends here. 
                   Due to CACHE instructions at play, the end indicated in
                   the for loop by pycdas is not correct, it is off by
                   some small amount. */
                if (curblock->blktype() == ASTBlock::BLK_FOR) {
                    if (blocks.size() > 1) {
                        PycRef<ASTBlock> prev = blocks.top();
                        blocks.pop();

                        curblock = blocks.top();
                        curblock->append(prev.cast<ASTNode>());
                        // for-else found at a duplicated break exit: the else body runs up to the recorded offset
                        auto fe = forElseEnd.find(prev.cast<ASTIterBlock>()->start());
                        if (fe != forElseEnd.end() && fe->second > pos) {
                            stack_hist.push(stack);
                            PycRef<ASTBlock> elseblk = new ASTBlock(ASTBlock::BLK_ELSE, fe->second);
                            elseblk->init();
                            blocks.push(elseblk);
                            curblock = blocks.top();
                        }
                    } else {
                        cleanBuild = false;
                    }
                }
                else {
                    bool for_still_open = false;
                    std::stack<PycRef<ASTBlock> > pending = blocks;
                    while (!pending.empty()) {
                        if (pending.top()->blktype() == ASTBlock::BLK_FOR) {
                            /* An enclosing outer loop is expected to remain
                               open when END_FOR cleans up a nested loop. Only
                               flag the nearest loop if its own extent has
                               already ended here. */
                            for_still_open = pending.top()->end() <= pos;
                            break;
                        }
                        pending.pop();
                    }

                    /* Python 3.12+ places END_FOR after the loop back-edge.
                       A correctly reconstructed loop has already been closed
                       there, so END_FOR only completes bytecode stack cleanup. */
                    if (for_still_open) {
                        fprintf(stderr, "Wrong block type %i for END_FOR in %s at %d\n",
                                curblock->blktype(),
                                code->name() != nullptr ? code->name()->value() : "<unknown>",
                                curpos);
                        cleanBuild = false;
                    }
                }
            }
            break;
        case Pyc::POP_TOP:
            {
                if (skipNextPopTop) {
                    skipNextPopTop = false;
                    break;
                }
                // await / yield / yield from is a statement only when its result is discarded
                if (!stack.empty() && stack.top() != nullptr
                        && (stack.top().type() == ASTNode::NODE_AWAITABLE
                            || ast_is_yield_expr(stack.top()))) {
                    PycRef<ASTNode> awaited = stack.top();
                    stack.pop();
                    curblock->append(awaited);
                    break;
                }
                if (suppressNextPopTop) {
                    suppressNextPopTop = false;
                    if (!stack.empty())
                        stack.pop();
                    break;
                }
                if (unpack) {
                    // 3.13+ compiles a dead unpack target (first _ in a, _, _ = x) as POP_TOP
                    PycRef<PycString> discard = new PycString(PycObject::TYPE_STRING);
                    discard->setValue("_");
                    if (ast_add_unpack_target(new ASTName(discard), unpack, unpackStar,
                                              stack, curblock))
                        break;
                }
                PycRef<ASTNode> value = stack.top();
                if (mod->verCompare(3, 12) >= 0 && value != nullptr) {
                    /* FOR_ITER keeps its hidden iterator on the value stack in
                       3.12+.  A return from the loop body discards that exact
                       node with POP_TOP before RETURN_CONST.  Do not print the
                       iterator as a bare source expression. */
                    PycRef<ASTNode> loopIter;
                    PycRef<ASTBlock> loopBlock;
                    bool innermostLoop = true;
                    std::stack<PycRef<ASTBlock> > pending = blocks;
                    while (!pending.empty()) {
                        if (pending.top()->blktype() == ASTBlock::BLK_FOR
                                || pending.top()->blktype()
                                    == ASTBlock::BLK_ASYNCFOR) {
                            // A return from nested loops pops the outer iterators as well
                            if (loopBlock == nullptr || pending.top().cast<ASTIterBlock>()->iter() == value) {
                                innermostLoop = loopBlock == nullptr;
                                loopIter = pending.top().cast<ASTIterBlock>()->iter();
                                loopBlock = pending.top();
                            }
                            if (loopIter == value)
                                break;
                        }
                        pending.pop();
                    }
                    // Handler decoded after its loop closed: the iterator still belongs to that loop
                    if (loopIter != value) {
                        for (const auto& f : forBlockAt) {
                            if (f.second.cast<ASTIterBlock>()->iter() == value) {
                                loopIter = value;
                                loopBlock = f.second;
                                innermostLoop = false;
                            }
                        }
                    }
                    // 3.15+ iterators take two stack slots: a POP_TOP pair drops one loop iterator
                    if (mod->verCompare(3, 15) >= 0 && loopIter != nullptr && value == loopIter) {
                        int pairOp = 0, pairArg = 0, pairNext = 0;
                        if (ast_read_wordcode_instr(code->code(), mod, pos, pairOp, pairArg, pairNext)
                                && pairOp == Pyc::POP_TOP) {
                            curpos = pos;
                            bc_next(source, mod, opcode, operand, pos);
                        }
                    }
                    // break whose short after-loop code was copied here (exit duplication): same code as at the loop exit
                    int dupElseEnd = 0;
                    int copyEnd = loopIter != nullptr && value == loopIter && innermostLoop
                            ? ast_duplicated_loop_exit(code, mod, pos, loopBlock->end(), dupElseEnd) : -1;
                    if (copyEnd > pos) {
                        if (dupElseEnd > 0)
                            forElseEnd[loopBlock.cast<ASTIterBlock>()->start()] = dupElseEnd;
                        stack.pop();
                        ast_break_dest(curblock, curpos)->append(new ASTKeyword(ASTKeyword::KW_BREAK));
                        while (pos < copyEnd && !source.atEof()) {
                            curpos = pos;
                            bc_next(source, mod, opcode, operand, pos);
                        }
                        break;
                    }
                    if (loopIter != nullptr && value == loopIter) {
                        PycBuffer lookahead(code->code()->value(),
                                code->code()->length());
                        int nextOp = 0, nextOperand = 0, nextPos = pos;
                        if (lookahead.setPos(source.pos())) {
                            bc_next(lookahead, mod, nextOp, nextOperand, nextPos);
                            // Outer loop iterators are popped before the same return
                            while ((nextOp == Pyc::CACHE || nextOp == Pyc::POP_TOP) && !lookahead.atEof())
                                bc_next(lookahead, mod, nextOp, nextOperand,
                                        nextPos);
                            bool returnsNext = nextOp == Pyc::RETURN_CONST_A
                                    || nextOp == Pyc::INSTRUMENTED_RETURN_CONST_A;
                            // 3.14+ has no RETURN_CONST: POP_TOP; LOAD_SMALL_INT/LOAD_CONST; RETURN_VALUE
                            if (!returnsNext && (nextOp == Pyc::LOAD_CONST_A
                                    || nextOp == Pyc::LOAD_SMALL_INT_A
                                    || nextOp == Pyc::LOAD_COMMON_CONSTANT_A)
                                    && !lookahead.atEof()) {
                                bc_next(lookahead, mod, nextOp, nextOperand, nextPos);
                                while (nextOp == Pyc::CACHE && !lookahead.atEof())
                                    bc_next(lookahead, mod, nextOp, nextOperand, nextPos);
                                returnsNext = nextOp == Pyc::RETURN_VALUE
                                        || nextOp == Pyc::INSTRUMENTED_RETURN_VALUE_A;
                            }
                            if (returnsNext) {
                                stack.pop();
                                break;
                            }
                        } else {
                            cleanBuild = false;
                        }
                    }
                }
                if (inlineCompActive && inlineCompCleanupOps > 0) {
                    inlineCompCleanupOps--;
                    break;
                }
                stack.pop();

                /* The live exception from PUSH_EXC_INFO is discarded here when
                   the handler has no `as` binding; never emit the sentinel. */
                if (isExcSentinel(value)) {
                    auto handlerCleanupEnd = [&](int handlerStart) {
                        for (const auto& cleanup : exception_entries) {
                            if (cleanup.push_lasti
                                    && cleanup.start_offset == handlerStart)
                                return cleanup.target;
                        }
                        return 0;
                    };
                    if (mod->verCompare(3, 11) >= 0
                            && curblock->blktype() == ASTBlock::BLK_CONTAINER
                            && curblock.cast<ASTContainerBlock>()->hasExcept()) {
                        stack_hist.push(stack);
                        int handlerStart = curblock.cast<ASTContainerBlock>()->except();
                        int handlerEnd = handlerCleanupEnd(handlerStart);
                        PycRef<ASTBlock> except =
                                new ASTCondBlock(ASTBlock::BLK_EXCEPT,
                                        handlerEnd, NULL, false);
                        except->init();
                        blocks.push(except);
                        curblock = blocks.top();
                    } else if (mod->verCompare(3, 11) >= 0
                            && curblock->blktype() == ASTBlock::BLK_EXCEPT) {
                        if (curblock->end() == 0 && blocks.size() > 1) {
                            std::stack<PycRef<ASTBlock> > pending = blocks;
                            pending.pop();
                            if (!pending.empty()
                                    && pending.top()->blktype()
                                        == ASTBlock::BLK_CONTAINER) {
                                int handlerStart = pending.top()
                                        .cast<ASTContainerBlock>()->except();
                                curblock->setEnd(handlerCleanupEnd(handlerStart));
                            }
                        }
                        if (!curblock->inited())
                            curblock->init();
                    } else if (!curblock->inited()) {
                        curblock->init();
                    }
                    break;
                }

                // 2.7+ `while True:` (SETUP_LOOP without a test) has no condition to pop: this is a body statement
                bool unconditionalWhile = curblock->blktype() == ASTBlock::BLK_WHILE && mod->verCompare(2, 7) >= 0
                        && curblock.cast<ASTCondBlock>()->cond() == nullptr;
                if (unconditionalWhile && !curblock->inited())
                    curblock->init();
                if (!curblock->inited()) {
                    if (curblock->blktype() == ASTBlock::BLK_WITH) {
                        curblock.cast<ASTWithBlock>()->setExpr(value);
                    } else {
                        curblock->init();
                    }
                    break;
                } else if (value == nullptr || value->processed()) {
                    break;
                }

                curblock->append(value);

                if (curblock->blktype() == ASTBlock::BLK_FOR
                        && curblock.cast<ASTIterBlock>()->isComprehension()) {
                    /* This relies on some really uncertain logic...
                     * If it's a comprehension, the only POP_TOP should be
                     * a call to append the iter to the list.
                     */
                    if (value.type() == ASTNode::NODE_CALL) {
                        auto& pparams = value.cast<ASTCall>()->pparams();
                        if (!pparams.empty()) {
                            PycRef<ASTNode> res = pparams.front();
                            stack.push(new ASTComprehension(res));
                        }
                    }
                }
            }
            break;
        case Pyc::PRINT_ITEM:
            {
                PycRef<ASTPrint> printNode;
                if (curblock->size() > 0 && curblock->nodes().back().type() == ASTNode::NODE_PRINT)
                    printNode = curblock->nodes().back().try_cast<ASTPrint>();
                if (printNode && printNode->stream() == nullptr && !printNode->eol())
                    printNode->add(stack.top());
                else
                    curblock->append(new ASTPrint(stack.top()));
                stack.pop();
            }
            break;
        case Pyc::PRINT_ITEM_TO:
            {
                PycRef<ASTNode> stream = stack.top();
                stack.pop();

                PycRef<ASTPrint> printNode;
                if (curblock->size() > 0 && curblock->nodes().back().type() == ASTNode::NODE_PRINT)
                    printNode = curblock->nodes().back().try_cast<ASTPrint>();
                if (printNode && printNode->stream() == stream && !printNode->eol())
                    printNode->add(stack.top());
                else
                    curblock->append(new ASTPrint(stack.top(), stream));
                stack.pop();
                if (stream)
                    stream->setProcessed();
            }
            break;
        case Pyc::PRINT_NEWLINE:
            {
                PycRef<ASTPrint> printNode;
                if (curblock->size() > 0 && curblock->nodes().back().type() == ASTNode::NODE_PRINT)
                    printNode = curblock->nodes().back().try_cast<ASTPrint>();
                if (printNode && printNode->stream() == nullptr && !printNode->eol())
                    printNode->setEol(true);
                else
                    curblock->append(new ASTPrint(nullptr));
                stack.pop();
            }
            break;
        case Pyc::PRINT_NEWLINE_TO:
            {
                PycRef<ASTNode> stream = stack.top();
                stack.pop();

                PycRef<ASTPrint> printNode;
                if (curblock->size() > 0 && curblock->nodes().back().type() == ASTNode::NODE_PRINT)
                    printNode = curblock->nodes().back().try_cast<ASTPrint>();
                if (printNode && printNode->stream() == stream && !printNode->eol())
                    printNode->setEol(true);
                else
                    curblock->append(new ASTPrint(nullptr, stream));
                stack.pop();
                if (stream)
                    stream->setProcessed();
            }
            break;
        case Pyc::RAISE_VARARGS_A:
            {
                ASTRaise::param_t paramList;
                for (int i = 0; i < operand; i++) {
                    paramList.push_front(stack.top());
                    stack.pop();
                }
                curblock->append(new ASTRaise(paramList));

                if ((curblock->blktype() == ASTBlock::BLK_IF
                        || curblock->blktype() == ASTBlock::BLK_ELSE)
                        && stack_hist.size()
                        && (mod->verCompare(2, 6) >= 0)) {
                    stack = stack_hist.top();
                    stack_hist.pop();

                    PycRef<ASTBlock> prev = curblock;
                    blocks.pop();
                    curblock = blocks.top();
                    curblock->append(prev.cast<ASTNode>());

                    // A jump still inside the closed block is dead code after the raise (the skip over an else)
                    int deadOp = 0, deadArg = 0, deadNext = 0;
                    if (pos < prev->end()
                            && ast_read_any_instr(code, mod, pos, deadOp, deadArg, deadNext)
                            && (deadOp == Pyc::JUMP_ABSOLUTE_A || deadOp == Pyc::JUMP_FORWARD_A
                                || deadOp == Pyc::JUMP_BACKWARD_A)
                            && ast_next_instr_offset_after_caches(mod, deadOp, deadNext) <= prev->end()) {
                        curpos = pos;
                        bc_next(source, mod, opcode, operand, pos);
                    }
                }
            }
            break;
        case Pyc::RETURN_VALUE:
        case Pyc::INSTRUMENTED_RETURN_VALUE_A:
            {
                auto finallyReturn = finallyReturnTryAt.find(curpos);
                PycRef<ASTNode> value;
                auto savedValue = finallyReturnValueAt.find(curpos);
                if (savedValue != finallyReturnValueAt.end()) {
                    value = savedValue->second;
                    finallyReturnValueAt.erase(savedValue);
                } else {
                    value = stack.top();
                    stack.pop();
                }
                PycRef<ASTNode> ret = new ASTReturn(value);
                if (finallyReturn != finallyReturnTryAt.end()) {
                    finallyReturn->second->append(ret);
                    finallyReturnTryAt.erase(finallyReturn);
                    auto skip = finallyReturnSkipAt.find(curpos);
                    if (skip != finallyReturnSkipAt.end()) {
                        with_skip_until = skip->second;
                        finallyReturnSkipAt.erase(skip);
                    }
                } else {
                    curblock->append(ret);
                }

                if ((curblock->blktype() == ASTBlock::BLK_IF
                        || curblock->blktype() == ASTBlock::BLK_ELSE)
                        && stack_hist.size()
                        && (mod->verCompare(2, 6) >= 0)) {
                    stack = stack_hist.top();
                    stack_hist.pop();

                    PycRef<ASTBlock> prev = curblock;
                    blocks.pop();
                    curblock = blocks.top();
                    curblock->append(prev.cast<ASTNode>());

                    /* A return inside an if/else is, in pre-3.11 bytecode,
                       followed by a redundant JUMP that skips the else branch;
                       that jump must be consumed. In 3.11+ the return usually
                       falls straight into real code (a sibling branch, the next
                       statement such as another `return`, or an exception
                       handler), and consuming it would silently drop that code.
                       Peek the next instruction and only skip it when it is an
                       actual unconditional jump; otherwise keep it. */
                    if (!source.atEof()) {
                        int savedSrc = source.pos();
                        int savedPos = pos;
                        int pkOp = 0, pkOperand = 0;
                        bc_next(source, mod, pkOp, pkOperand, pos);
                        bool keepNext = !(pkOp == Pyc::JUMP_FORWARD_A
                                       || pkOp == Pyc::JUMP_ABSOLUTE_A
                                       || pkOp == Pyc::JUMP_BACKWARD_A
                                       || pkOp == Pyc::JUMP_BACKWARD_NO_INTERRUPT_A);
                        // A backward jump here is the enclosing loop's back-edge, not a jump over an else branch
                        int pkTarget = -1;
                        if (pkOp == Pyc::JUMP_BACKWARD_A)
                            pkTarget = ast_relative_jump_target(mod, pkOp, pkOperand, pos, true);
                        else if (pkOp == Pyc::JUMP_ABSOLUTE_A)
                            pkTarget = mod->verCompare(3, 10) >= 0 ? pkOperand * 2 : pkOperand;
                        if (pkTarget >= 0 && pkTarget < savedPos) {
                            keepNext = true;
                            // A duplicated back-edge (3.12+) followed by another one to the same head is redundant
                            if (!source.atEof()) {
                                int src2 = source.pos(), pos2 = pos;
                                int op2 = 0, arg2 = 0;
                                bc_next(source, mod, op2, arg2, pos);
                                int t2 = op2 == Pyc::JUMP_BACKWARD_A ? ast_relative_jump_target(mod, op2, arg2, pos, true)
                                       : op2 == Pyc::JUMP_ABSOLUTE_A ? (mod->verCompare(3, 10) >= 0 ? arg2 * 2 : arg2) : -2;
                                if (t2 == pkTarget)
                                    keepNext = false;
                                if (!source.setPos(src2))
                                    cleanBuild = false;
                                pos = pos2;
                            }
                        }
                        if (keepNext) {
                            if (!source.setPos(savedSrc))
                                cleanBuild = false;
                            pos = savedPos;
                        } else {
                            opcode = pkOp;
                            operand = pkOperand;
                        }
                    }
                }
            }
            break;
        case Pyc::RETURN_CONST_A:
        case Pyc::INSTRUMENTED_RETURN_CONST_A:
            {
                PycRef<ASTObject> value = new ASTObject(code->getConst(operand));
                curblock->append(new ASTReturn(value.cast<ASTNode>()));
            }
            break;
        case Pyc::ROT_TWO:
            {
                PycRef<ASTNode> one = stack.top();
                stack.pop();
                if (stack.top().type() == ASTNode::NODE_CHAINSTORE) {
                    stack.pop();
                }
                PycRef<ASTNode> two = stack.top();
                stack.pop();

                stack.push(one);
                stack.push(two);
            }
            break;
        case Pyc::ROT_THREE:
            {
                PycRef<ASTNode> one = stack.top();
                stack.pop();
                // DUP_TOP; ROT_THREE feeds a chained comparison, not a chained assignment
                if (one.type() == ASTNode::NODE_CHAINSTORE) {
                    one = stack.top();
                    stack.pop();
                }
                PycRef<ASTNode> two = stack.top();
                stack.pop();
                if (stack.top().type() == ASTNode::NODE_CHAINSTORE) {
                    stack.pop();
                }
                PycRef<ASTNode> three = stack.top();
                stack.pop();
                stack.push(one);
                stack.push(three);
                stack.push(two);
            }
            break;
        case Pyc::ROT_FOUR:
            {
                // Pre-3.11 return from an except handler: ROT_FOUR tucks the value under the (unmodelled) exception entries
                if (mod->verCompare(3, 11) < 0) {
                    PycBuffer peek(code->code()->value(), code->code()->length());
                    int nextOp = 0, nextArg = 0, nextAt = pos, at = pos;
                    bool ok = peek.setPos(pos);
                    while (ok && !peek.atEof()) {
                        at = nextAt;
                        bc_next(peek, mod, nextOp, nextArg, nextAt);
                        if (!exceptAsSkip.count(at))
                            break;
                    }
                    if (ok && nextOp == Pyc::POP_EXCEPT)
                        break;
                }
                PycRef<ASTNode> one = stack.top();
                stack.pop();
                PycRef<ASTNode> two = stack.top();
                stack.pop();
                PycRef<ASTNode> three = stack.top();
                stack.pop();
                if (stack.top().type() == ASTNode::NODE_CHAINSTORE) {
                    stack.pop();
                }
                PycRef<ASTNode> four = stack.top();
                stack.pop();
                stack.push(one);
                stack.push(four);
                stack.push(three);
                stack.push(two);
            }
            break;
        case Pyc::SET_LINENO_A:
            // Ignore
            break;
        case Pyc::SETUP_WITH_A:
            {
                PycRef<ASTBlock> withblock = new ASTWithBlock(pos+operand);
                blocks.push(withblock);
                curblock = blocks.top();
            }
            break;
        case Pyc::WITH_EXCEPT_START:
            /* Python 3.11 with-statement exception cleanup: calls __exit__ with
               the live exception. Discard the exception sentinel that
               PUSH_EXC_INFO left on the stack and yield a None-like result so
               the implicit cleanup test does not leak the sentinel. */
            if (!stack.empty() && isExcSentinel(stack.top()))
                stack.pop();
            stack.push(nullptr);
            break;
        case Pyc::BEFORE_WITH:
            {
                /* Python 3.11 with-statement. If the pre-pass recognized this
                   one, open a with-block; the context manager stays on the
                   stack and the following STORE/POP_TOP turns it into the
                   with-expression (and optional `as <var>`). */
                auto it = withBodyEndByBefore.find(curpos);
                if (it != withBodyEndByBefore.end()) {
                    PycRef<ASTBlock> withblock = new ASTWithBlock(it->second);
                    blocks.push(withblock);
                    curblock = blocks.top();
                }
            }
            break;
        case Pyc::WITH_CLEANUP:
        case Pyc::WITH_CLEANUP_START:
            {
                // Stack top should be a None. Ignore it.
                PycRef<ASTNode> none = stack.top();
                stack.pop();

                if (none != NULL) {
                    /* Best-effort fallback for newer bytecode stack shapes. */
                    break;
                }

                if (curblock->blktype() == ASTBlock::BLK_WITH
                        && curblock->end() == curpos) {
                    PycRef<ASTBlock> with = curblock;
                    blocks.pop();
                    curblock = blocks.top();
                    curblock->append(with.cast<ASTNode>());
                }
                else {
                    /* Best-effort fallback for unmatched WITH_CLEANUP. */
                }
            }
            break;
        case Pyc::WITH_CLEANUP_FINISH:
            /* Ignore this */
            break;
        case Pyc::SETUP_EXCEPT_A:
            {
                if (curblock->blktype() == ASTBlock::BLK_CONTAINER) {
                    curblock.cast<ASTContainerBlock>()->setExcept(pos+operand);
                } else {
                    PycRef<ASTBlock> next = new ASTContainerBlock(0, pos+operand);
                    blocks.push(next.cast<ASTBlock>());
                }

                /* Store the current stack for the except/finally statement(s) */
                stack_hist.push(stack);
                PycRef<ASTBlock> tryblock = new ASTBlock(ASTBlock::BLK_TRY, pos+operand, true);
                blocks.push(tryblock.cast<ASTBlock>());
                curblock = blocks.top();

                need_try = false;
            }
            break;
        case Pyc::SETUP_FINALLY_A:
            if (exceptSetups.count(curpos)) {
                // 3.8-3.10 try/except: same structure as SETUP_EXCEPT in older versions
                int handler = ast_relative_jump_target(mod, opcode, operand, pos, false);
                if (curblock->blktype() == ASTBlock::BLK_CONTAINER
                        && !curblock.cast<ASTContainerBlock>()->hasExcept()) {
                    curblock.cast<ASTContainerBlock>()->setExcept(handler);
                } else {
                    PycRef<ASTBlock> next = new ASTContainerBlock(0, handler);
                    blocks.push(next.cast<ASTBlock>());
                }
                stack_hist.push(stack);
                PycRef<ASTBlock> tryblock = new ASTBlock(ASTBlock::BLK_TRY, handler, true);
                blocks.push(tryblock.cast<ASTBlock>());
                curblock = blocks.top();
                need_try = false;
                break;
            }
            {
                if (mod->verCompare(3, 9) >= 0 && mod->verCompare(3, 11) < 0
                        && curblock->blktype() == ASTBlock::BLK_EXCEPT) {
                    py39_handler_cleanup_target = pos + (mod->verCompare(3, 10) >= 0
                                                  ? operand * (int)sizeof(uint16_t)
                                                  : operand);
                    break;
                }

                PycRef<ASTBlock> next = new ASTContainerBlock(
                        ast_relative_jump_target(mod, opcode, operand, pos, false));
                blocks.push(next.cast<ASTBlock>());
                curblock = blocks.top();

                need_try = true;
            }
            break;
        case Pyc::SETUP_LOOP_A:
            {
                PycRef<ASTBlock> next = new ASTCondBlock(ASTBlock::BLK_WHILE, pos+operand, NULL, false);
                blocks.push(next.cast<ASTBlock>());
                curblock = blocks.top();
            }
            break;
        case Pyc::SLICE_0:
            {
                PycRef<ASTNode> name = stack.top();
                stack.pop();

                PycRef<ASTNode> slice = new ASTSlice(ASTSlice::SLICE0);
                stack.push(new ASTSubscr(name, slice));
            }
            break;
        case Pyc::SLICE_1:
            {
                PycRef<ASTNode> lower = stack.top();
                stack.pop();
                PycRef<ASTNode> name = stack.top();
                stack.pop();

                PycRef<ASTNode> slice = new ASTSlice(ASTSlice::SLICE1, lower);
                stack.push(new ASTSubscr(name, slice));
            }
            break;
        case Pyc::SLICE_2:
            {
                PycRef<ASTNode> upper = stack.top();
                stack.pop();
                PycRef<ASTNode> name = stack.top();
                stack.pop();

                PycRef<ASTNode> slice = new ASTSlice(ASTSlice::SLICE2, NULL, upper);
                stack.push(new ASTSubscr(name, slice));
            }
            break;
        case Pyc::SLICE_3:
            {
                PycRef<ASTNode> upper = stack.top();
                stack.pop();
                PycRef<ASTNode> lower = stack.top();
                stack.pop();
                PycRef<ASTNode> name = stack.top();
                stack.pop();

                PycRef<ASTNode> slice = new ASTSlice(ASTSlice::SLICE3, lower, upper);
                stack.push(new ASTSubscr(name, slice));
            }
            break;
        case Pyc::STORE_ATTR_A:
            {
                if (unpack) {
                    PycRef<ASTNode> name = stack.top();
                    stack.pop();
                    PycRef<ASTNode> attr = new ASTBinary(name, new ASTName(code->getName(operand)), ASTBinary::BIN_ATTR);
                    if (unpack == unpackStar)
                        attr = new ASTUnary(attr, ASTUnary::UN_STAR);

                    PycRef<ASTNode> tup = stack.top();
                    if (tup.type() == ASTNode::NODE_TUPLE)
                        tup.cast<ASTTuple>()->add(attr);
                    else {
                        cleanBuild = false;
                    }

                    if (--unpack <= 0) {
                        if (unpackStar >= 0)
                            tup.cast<ASTTuple>()->setRequireParens(false);
                        stack.pop();
                        bool seqDup = stack.top_is_dup();
                        PycRef<ASTNode> seq = stack.top();
                        stack.pop();
                        if (seq != nullptr && ast_keep_chain_target(seq, tup, stack, mod, seqDup)) {
                        } else if (seq.type() == ASTNode::NODE_CHAINSTORE) {
                            append_to_chain_store(seq, tup, stack, curblock);
                        } else {
                            curblock->append(new ASTStore(seq, tup));
                        }
                    }
                } else {
                    PycRef<ASTNode> name = stack.top();
                    stack.pop();
                    bool valueDup = stack.top_is_dup();
                    PycRef<ASTNode> value = stack.top();
                    stack.pop();
                    PycRef<ASTNode> attr = new ASTBinary(name, new ASTName(code->getName(operand)), ASTBinary::BIN_ATTR);
                    if (ast_keep_chain_target(value, attr, stack, mod, valueDup)) {
                        break;
                    } else if (value.type() == ASTNode::NODE_CHAINSTORE) {
                        append_to_chain_store(value, attr, stack, curblock);
                    } else {
                        curblock->append(new ASTStore(value, attr));
                    }
                }
            }
            break;
        case Pyc::STORE_DEREF_A:
            {
                if (unpack) {
                    PycRef<ASTNode> name = new ASTName(code->getCellVar(mod, operand));
                    if (unpack == unpackStar)
                        name = new ASTUnary(name, ASTUnary::UN_STAR);

                    PycRef<ASTNode> tup = stack.top();
                    if (tup.type() == ASTNode::NODE_TUPLE)
                        tup.cast<ASTTuple>()->add(name);
                    else {
                        cleanBuild = false;
                    }

                    if (--unpack <= 0) {
                        if (unpackStar >= 0)
                            tup.cast<ASTTuple>()->setRequireParens(false);
                        stack.pop();
                        bool seqDup = stack.top_is_dup();
                        PycRef<ASTNode> seq = stack.top();
                        stack.pop();

                        if (seq != nullptr && ast_keep_chain_target(seq, tup, stack, mod, seqDup)) {
                        } else if (seq.type() == ASTNode::NODE_CHAINSTORE) {
                            append_to_chain_store(seq, tup, stack, curblock);
                        } else {
                            curblock->append(new ASTStore(seq, tup));
                        }
                    }
                } else {
                    bool valueDup = stack.top_is_dup();
                    PycRef<ASTNode> value = stack.top();
                    stack.pop();
                    PycRef<PycString> cellName = code->getCellVar(mod, operand);
                    if (py313ClassBody && cellName->strValue() == "__classdict__")
                        break;
                    PycRef<ASTNode> name = new ASTName(cellName);

                    if (py311_except_bind_pending && mod->verCompare(3, 11) >= 0) {
                        PycRef<ASTCondBlock> except = ast_find_except_bind_block(curblock, blocks);
                        if (except != nullptr) {
                            except->setExceptVar(name);
                            py311_except_bound_names.insert(
                                    name.cast<ASTName>()->name()->strValue());
                            py311_except_bind_pending = false;
                            break;
                        }
                    }

                    if (ast_store_named_expr(value, name, stack, mod, valueDup, code, pos)) {
                    } else if (value.type() == ASTNode::NODE_CHAINSTORE) {
                        append_to_chain_store(value, name, stack, curblock);
                    } else if (!ast_attach_decorators(curblock, value, name)) {
                        curblock->append(new ASTStore(value, name));
                    }
                    ast_drop_named_dup(stack, code, mod, pos);
                }
            }
            break;
        case Pyc::STORE_FAST_LOAD_FAST_A:
            if (unpack && ast_add_unpack_target(new ASTName(code->getLocal(operand >> 4)),
                                                unpack, unpackStar, stack, curblock)) {
                stack.push(new ASTName(code->getLocal(operand & 0xF)));
                break;
            }
            {
                bool valueDup = stack.top_is_dup();
                PycRef<ASTNode> value = stack.top();
                stack.pop();
                PycRef<ASTNode> dest = new ASTName(code->getLocal(operand >> 4));
                if ((curblock->blktype() == ASTBlock::BLK_FOR
                            || (mod->verCompare(3, 11) >= 0
                                && curblock->blktype() == ASTBlock::BLK_ASYNCFOR))
                        && !curblock->inited()) {
                    curblock.cast<ASTIterBlock>()->setIndex(dest);
                } else if (curblock->blktype() == ASTBlock::BLK_WITH
                        && !curblock->inited()) {
                    PycRef<ASTNode> expr = value;
                    if (value.type() == ASTNode::NODE_CALL) {
                        PycRef<ASTNode> func = value.cast<ASTCall>()->func();
                        if (func.type() == ASTNode::NODE_BINARY
                                && func.cast<ASTBinary>()->op() == ASTBinary::BIN_ATTR
                                && func.cast<ASTBinary>()->right().type() == ASTNode::NODE_NAME
                                && func.cast<ASTBinary>()->right().cast<ASTName>()->name()
                                        ->isEqual("__enter__")) {
                            expr = func.cast<ASTBinary>()->left();
                        }
                    }
                    curblock.cast<ASTWithBlock>()->setExpr(expr);
                    curblock.cast<ASTWithBlock>()->setVar(dest);
                } else if (mod->verCompare(3, 8) >= 0 && valueDup && value != nullptr
                        && !stack.empty() && stack.top() == value) {
                    // COPY; STORE_FAST_LOAD_FAST. Same local reloaded is (x := v); a different local is b = ... = v
                    stack.pop();
                    ASTNodeList::list_t targets;
                    PycRef<ASTChainStore> named = new ASTChainStore(targets, value);
                    named->append(dest);
                    if ((operand >> 4) == (operand & 0xF))
                        named->setExpression(true);
                    stack.push(named.cast<ASTNode>());
                    stack.push(new ASTName(code->getLocal(operand & 0xF)));
                    break;
                } else {
                    curblock->append(new ASTStore(value, dest));
                }
                stack.push(new ASTName(code->getLocal(operand & 0xF)));
            }
            break;
        case Pyc::STORE_FAST_STORE_FAST_A:
            {
                if (unpack >= 2) {
                    PycRef<ASTTuple> tuple = stack.top().try_cast<ASTTuple>();
                    if (tuple != nullptr) {
                        tuple->add(new ASTName(code->getLocal(operand >> 4)));
                        tuple->add(new ASTName(code->getLocal(operand & 0xF)));
                        unpack -= 2;
                        if (unpack == 0) {
                            tuple->setRequireParens(false);
                            stack.pop();
                            PycRef<ASTNode> seq;
                            bool seqDup = false;
                            if (!stack.empty()) {
                                seqDup = stack.top_is_dup();
                                seq = stack.top();
                                stack.pop();
                            }
                            if (curblock->blktype() == ASTBlock::BLK_FOR
                                    && !curblock->inited()) {
                                curblock.cast<ASTIterBlock>()->setIndex(tuple.cast<ASTNode>());
                            } else if (seq != nullptr && ast_keep_chain_target(seq, tuple.cast<ASTNode>(), stack, mod, seqDup)) {
                                // a, b = c = g(): the copy left under the unpack is the same value
                            } else if (seq != nullptr) {
                                curblock->append(new ASTStore(seq, tuple.cast<ASTNode>()));
                            }
                        }
                        break;
                    }
                }
                bool value2Dup = stack.top_is_dup();
                PycRef<ASTNode> value2 = stack.top();
                stack.pop();
                bool hadTwo = !stack.empty();
                PycRef<ASTNode> value1 = hadTwo ? stack.top() : nullptr;
                if (hadTwo)
                    stack.pop();
                // COPY 1; STORE_FAST_STORE_FAST is a = b = value, one evaluation
                // Two nulls are one None only when COPY 1 recorded the top slot
                if (hadTwo && value2Dup && value1 == value2 && mod->verCompare(3, 8) >= 0) {
                    if (value2 != nullptr && value2.type() == ASTNode::NODE_CHAINSTORE) {
                        value2.cast<ASTChainStore>()->append(new ASTName(code->getLocal(operand >> 4)));
                        value2.cast<ASTChainStore>()->append(new ASTName(code->getLocal(operand & 0xF)));
                        curblock->append(value2);
                        break;
                    }
                    if (value1 == nullptr)
                        value1 = new ASTObject(Pyc_None);
                    ASTNodeList::list_t targets;
                    PycRef<ASTChainStore> chain = new ASTChainStore(targets, value1);
                    chain->append(new ASTName(code->getLocal(operand >> 4)));
                    chain->append(new ASTName(code->getLocal(operand & 0xF)));
                    curblock->append(chain.cast<ASTNode>());
                    break;
                }
                curblock->append(new ASTStore(value1, new ASTName(code->getLocal(operand >> 4))));
                curblock->append(new ASTStore(value2, new ASTName(code->getLocal(operand & 0xF))));
            }
            break;
        case Pyc::STORE_FAST_A:
            {
                if (inlineCompRestoreStores.count(curpos)) {
                    if (!stack.empty())
                        stack.pop();
                    break;
                }
                if (unpack) {
                    PycRef<ASTNode> name;

                    if (mod->verCompare(1, 3) < 0)
                        name = new ASTName(code->getName(operand));
                    else
                        name = new ASTName(code->getLocal(operand));
                    if (unpack == unpackStar)
                        name = new ASTUnary(name, ASTUnary::UN_STAR);

                    PycRef<ASTNode> tup = stack.top();
                    if (tup.type() == ASTNode::NODE_TUPLE)
                        tup.cast<ASTTuple>()->add(name);
                    else {
                        cleanBuild = false;
                    }

                    if (--unpack <= 0) {
                        if (unpackStar >= 0)
                            tup.cast<ASTTuple>()->setRequireParens(false);
                        stack.pop();
                        bool seqDup = stack.top_is_dup();
                        PycRef<ASTNode> seq = stack.top();
                        stack.pop();

                        if (curblock->blktype() == ASTBlock::BLK_FOR
                                && !curblock->inited()) {
                            PycRef<ASTTuple> tuple = tup.try_cast<ASTTuple>();
                            if (tuple != NULL)
                                tuple->setRequireParens(false);
                            curblock.cast<ASTIterBlock>()->setIndex(tup);
                        } else if (seq != nullptr && ast_keep_chain_target(seq, tup, stack, mod, seqDup)) {
                        } else if (seq.type() == ASTNode::NODE_CHAINSTORE) {
                            append_to_chain_store(seq, tup, stack, curblock);
                        } else {
                            curblock->append(new ASTStore(seq, tup));
                        }
                    }
                } else {
                    bool valueDup = stack.top_is_dup();
                    PycRef<ASTNode> value = stack.top();
                    stack.pop();
                    PycRef<ASTNode> name;

                    if (mod->verCompare(1, 3) < 0)
                        name = new ASTName(code->getName(operand));
                    else
                        name = new ASTName(code->getLocal(operand));

                    if (py39_except_bind_pending
                            && mod->verCompare(3, 9) >= 0 && mod->verCompare(3, 11) < 0
                            && curblock->blktype() == ASTBlock::BLK_EXCEPT) {
                        py39_except_bind_pending = false;
                        py39_except_cleanup_var = operand;
                        break;
                    }

                    if (py311_except_bind_pending && mod->verCompare(3, 11) >= 0) {
                        PycRef<ASTCondBlock> except = ast_find_except_bind_block(curblock, blocks);
                        if (except != nullptr) {
                            except->setExceptVar(name);
                            py311_except_bound_names.insert(
                                    name.cast<ASTName>()->name()->strValue());
                            py311_except_bind_pending = false;
                            break;
                        }
                    }

                    if (name.cast<ASTName>()->name()->value()[0] == '_'
                            && name.cast<ASTName>()->name()->value()[1] == '[') {
                        /* Don't show stores of list comp append objects. */
                        break;
                    }

                    if (handleExceptBinding(curblock, value, name))
                        break;

                    if ((curblock->blktype() == ASTBlock::BLK_FOR
                                || (mod->verCompare(3, 11) >= 0
                                    && curblock->blktype() == ASTBlock::BLK_ASYNCFOR))
                            && !curblock->inited()) {
                        curblock.cast<ASTIterBlock>()->setIndex(name);
                    } else if (!stack.empty()
                            && stack.top().type() == ASTNode::NODE_IMPORT
                            && value.type() != ASTNode::NODE_IMPORT) {
                        PycRef<ASTImport> import = stack.top().cast<ASTImport>();
                        import->add_store(new ASTStore(value, name));
                    } else if (curblock->blktype() == ASTBlock::BLK_WITH
                                   && !curblock->inited()) {
                        PycRef<ASTNode> expr = value;
                        if (value.type() == ASTNode::NODE_CALL) {
                            PycRef<ASTNode> func = value.cast<ASTCall>()->func();
                            if (func.type() == ASTNode::NODE_BINARY
                                    && func.cast<ASTBinary>()->op() == ASTBinary::BIN_ATTR
                                    && func.cast<ASTBinary>()->right().type() == ASTNode::NODE_NAME
                                    && func.cast<ASTBinary>()->right().cast<ASTName>()->name()
                                            ->isEqual("__enter__")) {
                                expr = func.cast<ASTBinary>()->left();
                            }
                        }
                        curblock.cast<ASTWithBlock>()->setExpr(expr);
                        curblock.cast<ASTWithBlock>()->setVar(name);
                    } else if (ast_store_named_expr(value, name, stack, mod, valueDup, code, pos)) {
                    } else if (value.type() == ASTNode::NODE_CHAINSTORE) {
                        append_to_chain_store(value, name, stack, curblock);
                    } else if (!ast_attach_decorators(curblock, value, name)) {
                        curblock->append(new ASTStore(value, name));
                    }
                    ast_drop_named_dup(stack, code, mod, pos);
                }
            }
            break;
        case Pyc::STORE_GLOBAL_A:
            {
                PycRef<ASTNode> name = new ASTName(code->getName(operand));
                PycRef<PycString> globalName = name.cast<ASTName>()->name();

                if (unpack) {
                    if (unpack == unpackStar)
                        name = new ASTUnary(name, ASTUnary::UN_STAR);
                    PycRef<ASTNode> tup = stack.top();
                    if (tup.type() == ASTNode::NODE_TUPLE)
                        tup.cast<ASTTuple>()->add(name);
                    else {
                        cleanBuild = false;
                    }

                    if (--unpack <= 0) {
                        if (unpackStar >= 0)
                            tup.cast<ASTTuple>()->setRequireParens(false);
                        stack.pop();
                        bool seqDup = stack.top_is_dup();
                        PycRef<ASTNode> seq = stack.top();
                        stack.pop();

                        if (curblock->blktype() == ASTBlock::BLK_FOR
                                && !curblock->inited()) {
                            PycRef<ASTTuple> tuple = tup.try_cast<ASTTuple>();
                            if (tuple != NULL)
                                tuple->setRequireParens(false);
                            curblock.cast<ASTIterBlock>()->setIndex(tup);
                        } else if (seq != nullptr && ast_keep_chain_target(seq, tup, stack, mod, seqDup)) {
                        } else if (seq.type() == ASTNode::NODE_CHAINSTORE) {
                            append_to_chain_store(seq, tup, stack, curblock);
                        } else {
                            curblock->append(new ASTStore(seq, tup));
                        }
                    }
                } else {
                    bool valueDup = stack.top_is_dup();
                    PycRef<ASTNode> value = stack.top();
                    stack.pop();
                    if (ast_store_named_expr(value, name, stack, mod, valueDup, code, pos)) {
                    } else if (value.type() == ASTNode::NODE_CHAINSTORE) {
                        append_to_chain_store(value, name, stack, curblock);
                    } else if (!ast_attach_decorators(curblock, value, name)) {
                        curblock->append(new ASTStore(value, name));
                    }
                    ast_drop_named_dup(stack, code, mod, pos);
                }

                /* Mark the global as used */
                code->markGlobal(globalName);
            }
            break;
        case Pyc::STORE_NAME_A:
            {
                if (unpack) {
                    PycRef<ASTNode> name = new ASTName(code->getName(operand));
                    if (unpack == unpackStar)
                        name = new ASTUnary(name, ASTUnary::UN_STAR);

                    PycRef<ASTNode> tup = stack.top();
                    if (tup.type() == ASTNode::NODE_TUPLE)
                        tup.cast<ASTTuple>()->add(name);
                    else {
                        cleanBuild = false;
                    }

                    if (--unpack <= 0) {
                        if (unpackStar >= 0)
                            tup.cast<ASTTuple>()->setRequireParens(false);
                        stack.pop();
                        bool seqDup = stack.top_is_dup();
                        PycRef<ASTNode> seq = stack.top();
                        stack.pop();

                        if (curblock->blktype() == ASTBlock::BLK_FOR
                                && !curblock->inited()) {
                            PycRef<ASTTuple> tuple = tup.try_cast<ASTTuple>();
                            if (tuple != NULL)
                                tuple->setRequireParens(false);
                            curblock.cast<ASTIterBlock>()->setIndex(tup);
                        } else if (seq != nullptr && ast_keep_chain_target(seq, tup, stack, mod, seqDup)) {
                        } else if (seq.type() == ASTNode::NODE_CHAINSTORE) {
                            append_to_chain_store(seq, tup, stack, curblock);
                        } else {
                            curblock->append(new ASTStore(seq, tup));
                        }
                    }
                } else {
                    bool valueDup = stack.top_is_dup();
                    PycRef<ASTNode> value = stack.top();
                    stack.pop();

                    PycRef<PycString> varname = code->getName(operand);
                    if (varname->length() >= 2 && varname->value()[0] == '_'
                            && varname->value()[1] == '[') {
                        /* Don't show stores of list comp append objects. */
                        break;
                    }
                    if (py313ClassBody
                            && (varname->strValue() == "__firstlineno__"
                                || varname->strValue() == "__classdict__"
                                || varname->strValue() == "__static_attributes__"
                                || varname->strValue() == "__classdictcell__")) {
                        // 3.13+ compiler-generated class-body bookkeeping, not part of the source
                        break;
                    }

                    PycRef<ASTNode> name = new ASTName(varname);

                    if (handleExceptBinding(curblock, value, name))
                        break;

                    if (curblock->blktype() == ASTBlock::BLK_FOR
                            && !curblock->inited()) {
                        curblock.cast<ASTIterBlock>()->setIndex(name);
                    } else if (stack.top().type() == ASTNode::NODE_IMPORT
                            && value.type() != ASTNode::NODE_IMPORT) {
                        PycRef<ASTImport> import = stack.top().cast<ASTImport>();

                        import->add_store(new ASTStore(value, name));
                    } else if (curblock->blktype() == ASTBlock::BLK_WITH
                               && !curblock->inited()) {
                        curblock.cast<ASTWithBlock>()->setExpr(value);
                        curblock.cast<ASTWithBlock>()->setVar(name);
                    } else if (ast_store_named_expr(value, name, stack, mod, valueDup, code, pos)) {
                    } else if (value.type() == ASTNode::NODE_CHAINSTORE) {
                        append_to_chain_store(value, name, stack, curblock);
                    } else if (!ast_attach_decorators(curblock, value, name)) {
                        curblock->append(new ASTStore(value, name));

                        if (value.type() == ASTNode::NODE_INVALID)
                            break;
                    }
                    ast_drop_named_dup(stack, code, mod, pos);
                }
            }
            break;
        case Pyc::STORE_SLICE_0:
            {
                PycRef<ASTNode> dest = stack.top();
                stack.pop();
                PycRef<ASTNode> value = stack.top();
                stack.pop();

                curblock->append(new ASTStore(value, new ASTSubscr(dest, new ASTSlice(ASTSlice::SLICE0))));
            }
            break;
        case Pyc::STORE_SLICE_1:
            {
                PycRef<ASTNode> upper = stack.top();
                stack.pop();
                PycRef<ASTNode> dest = stack.top();
                stack.pop();
                PycRef<ASTNode> value = stack.top();
                stack.pop();

                curblock->append(new ASTStore(value, new ASTSubscr(dest, new ASTSlice(ASTSlice::SLICE1, upper))));
            }
            break;
        case Pyc::STORE_SLICE_2:
            {
                PycRef<ASTNode> lower = stack.top();
                stack.pop();
                PycRef<ASTNode> dest = stack.top();
                stack.pop();
                PycRef<ASTNode> value = stack.top();
                stack.pop();

                curblock->append(new ASTStore(value, new ASTSubscr(dest, new ASTSlice(ASTSlice::SLICE2, NULL, lower))));
            }
            break;
        case Pyc::STORE_SLICE_3:
            {
                PycRef<ASTNode> lower = stack.top();
                stack.pop();
                PycRef<ASTNode> upper = stack.top();
                stack.pop();
                PycRef<ASTNode> dest = stack.top();
                stack.pop();
                PycRef<ASTNode> value = stack.top();
                stack.pop();

                curblock->append(new ASTStore(value, new ASTSubscr(dest, new ASTSlice(ASTSlice::SLICE3, upper, lower))));
            }
            break;
        case Pyc::STORE_SUBSCR:
            {
                if (unpack) {
                    PycRef<ASTNode> subscr = stack.top();
                    stack.pop();
                    PycRef<ASTNode> dest = stack.top();
                    stack.pop();

                    PycRef<ASTNode> save = new ASTSubscr(dest, subscr);
                    if (unpack == unpackStar)
                        save = new ASTUnary(save, ASTUnary::UN_STAR);

                    PycRef<ASTNode> tup = stack.top();
                    if (tup.type() == ASTNode::NODE_TUPLE)
                        tup.cast<ASTTuple>()->add(save);
                    else {
                        cleanBuild = false;
                    }

                    if (--unpack <= 0) {
                        if (unpackStar >= 0)
                            tup.cast<ASTTuple>()->setRequireParens(false);
                        stack.pop();
                        bool seqDup = stack.top_is_dup();
                        PycRef<ASTNode> seq = stack.top();
                        stack.pop();
                        if (seq != nullptr && ast_keep_chain_target(seq, tup, stack, mod, seqDup)) {
                        } else if (seq.type() == ASTNode::NODE_CHAINSTORE) {
                            append_to_chain_store(seq, tup, stack, curblock);
                        } else {
                            curblock->append(new ASTStore(seq, tup));
                        }
                    }
                } else {
                    PycRef<ASTNode> subscr = stack.top();
                    stack.pop();
                    PycRef<ASTNode> dest = stack.top();
                    stack.pop();
                    bool srcDup = stack.top_is_dup();
                    PycRef<ASTNode> src = stack.top();
                    stack.pop();

                    // If variable annotations are enabled, we'll need to check for them here.
                    // Python handles a varaible annotation by setting:
                    // __annotations__['var-name'] = type
                    const bool found_annotated_var = (variable_annotations && dest->type() == ASTNode::Type::NODE_NAME
                                                      && dest.cast<ASTName>()->name()->isEqual("__annotations__"));

                    if (found_annotated_var) {
                        // Annotations can be done alone or as part of an assignment.
                        // In the case of an assignment, we'll see a NODE_STORE on the stack.
                        if (!curblock->nodes().empty() && curblock->nodes().back()->type() == ASTNode::Type::NODE_STORE) {
                            // Replace the existing NODE_STORE with a new one that includes the annotation.
                            PycRef<ASTStore> store = curblock->nodes().back().cast<ASTStore>();
                            curblock->removeLast();
                            curblock->append(new ASTStore(store->src(),
                                                          new ASTAnnotatedVar(subscr, src)));
                        } else {
                            curblock->append(new ASTAnnotatedVar(subscr, src));
                        }
                    } else {
                        if (ast_keep_chain_target(src, new ASTSubscr(dest, subscr), stack, mod, srcDup)) {
                            break;
                        } else if (dest.type() == ASTNode::NODE_MAP) {
                            dest.cast<ASTMap>()->add(subscr, src);
                        } else if (src.type() == ASTNode::NODE_CHAINSTORE) {
                            append_to_chain_store(src, new ASTSubscr(dest, subscr), stack, curblock);
                        } else {
                            curblock->append(new ASTStore(src, new ASTSubscr(dest, subscr)));
                        }
                    }
                }
            }
            break;
        case Pyc::UNARY_CALL:
            {
                PycRef<ASTNode> func = stack.top();
                stack.pop();
                stack.push(new ASTCall(func, ASTCall::pparam_t(), ASTCall::kwparam_t()));
            }
            break;
        case Pyc::UNARY_CONVERT:
            {
                PycRef<ASTNode> name = stack.top();
                stack.pop();
                stack.push(new ASTConvert(name));
            }
            break;
        case Pyc::UNARY_INVERT:
            {
                PycRef<ASTNode> arg = stack.top();
                stack.pop();
                stack.push(new ASTUnary(arg, ASTUnary::UN_INVERT));
            }
            break;
        case Pyc::UNARY_NEGATIVE:
            {
                PycRef<ASTNode> arg = stack.top();
                stack.pop();
                stack.push(new ASTUnary(arg, ASTUnary::UN_NEGATIVE));
            }
            break;
        case Pyc::UNARY_NOT:
            {
                PycRef<ASTNode> arg = stack.top();
                stack.pop();
                stack.push(new ASTUnary(arg, ASTUnary::UN_NOT));
            }
            break;
        case Pyc::UNARY_POSITIVE:
            {
                PycRef<ASTNode> arg = stack.top();
                stack.pop();
                stack.push(new ASTUnary(arg, ASTUnary::UN_POSITIVE));
            }
            break;
        case Pyc::UNPACK_LIST_A:
        case Pyc::UNPACK_TUPLE_A:
        case Pyc::UNPACK_SEQUENCE_A:
            {
                unpack = operand;
                unpackStar = -1;
                if (unpack > 0) {
                    ASTTuple::value_t vals;
                    stack.push(new ASTTuple(vals));
                } else {
                    // Unpack zero values and assign it to top of stack or for loop variable.
                    // E.g. [] = TOS / for [] in X
                    ASTTuple::value_t vals;
                    auto tup = new ASTTuple(vals);
                    if (curblock->blktype() == ASTBlock::BLK_FOR
                        && !curblock->inited()) {
                        tup->setRequireParens(true);
                        curblock.cast<ASTIterBlock>()->setIndex(tup);
                    } else if (stack.top().type() == ASTNode::NODE_CHAINSTORE) {
                        auto chainStore = stack.top();
                        stack.pop();
                        append_to_chain_store(chainStore, tup, stack, curblock);
                    } else {
                        curblock->append(new ASTStore(stack.top(), tup));
                        stack.pop();
                    }
                }
            }
            break;
        case Pyc::UNPACK_EX_A:
            {
                int countBefore = operand & 0xFF;
                int countAfter = (operand >> 8) & 0xFF;
                unpack = countBefore + 1 + countAfter;
                unpackStar = countAfter + 1;
                ASTTuple::value_t vals;
                stack.push(new ASTTuple(vals));
            }
            break;
        case Pyc::YIELD_FROM:
            {
                // 3.5-3.10 await and yield from: pop the sent None and keep the result for POP_TOP or a store
                if (stack.empty()) {
                    cleanBuild = false;
                    break;
                }
                stack.pop();
                if (stack.empty()) {
                    cleanBuild = false;
                    break;
                }
                // A null placeholder (3.7 async-for) stays put. An awaitable is already the result.
                PycRef<ASTNode> value = stack.top();
                if (value == nullptr || value.type() == ASTNode::NODE_AWAITABLE)
                    break;
                stack.pop();
                stack.push(new ASTAwaitable(value, true));
            }
            break;
        case Pyc::YIELD_VALUE:
        case Pyc::YIELD_VALUE_A:
        case Pyc::INSTRUMENTED_YIELD_VALUE_A:
            {
                // The result is None for a bare yield statement, or the sent value when stored
                if (stack.empty()) {
                    cleanBuild = false;
                    break;
                }
                PycRef<ASTNode> value = stack.top();
                stack.pop();
                stack.push(new ASTReturn(value, ASTReturn::YIELD));
            }
            break;
        case Pyc::SETUP_ANNOTATIONS:
            variable_annotations = true;
            break;
        case Pyc::PRECALL_A:
        case Pyc::RESUME_A:
        case Pyc::INSTRUMENTED_RESUME_A:
            /* We just entirely ignore this / no-op */
            break;
        case Pyc::CACHE:
            /* These "fake" opcodes are used as placeholders for optimizing
               certain opcodes in Python 3.11+.  Since we have no need for
               that during disassembly/decompilation, we can just treat these
               as no-ops. */
            break;
        case Pyc::PUSH_NULL:
            stack.push(nullptr);
            break;
        case Pyc::GEN_START_A:
            stack.pop();
            break;
        case Pyc::SWAP_A:
            /* Python 3.11+: swap TOS with the operand-th element from the top.
               A plain stack operation (used by chained comparisons, starred
               unpacking, etc.). */
            if (mod->verCompare(3, 11) >= 0 && operand == 2
                    && curblock->blktype() == ASTBlock::BLK_EXCEPT) {
                /* Python 3.13 emits LOAD <return-value>; SWAP 2; POP_EXCEPT;
                   RETURN_VALUE for a return from an except clause.  POP_EXCEPT
                   removes interpreter exception state, not the Python return
                   value; applying the raw swap to the AST stack instead makes
                   an unrelated saved context become the returned expression. */
                PycBuffer lookahead(code->code()->value(), code->code()->length());
                int nextOp = 0, nextOperand = 0, nextPos = pos;
                if (lookahead.setPos(source.pos())) {
                    bc_next(lookahead, mod, nextOp, nextOperand, nextPos);
                    while (nextOp == Pyc::CACHE && !lookahead.atEof())
                        bc_next(lookahead, mod, nextOp, nextOperand, nextPos);
                    if (nextOp == Pyc::POP_EXCEPT) {
                        // `except E as name` adds name = None; del name before the return
                        int cleanupOps = 0;
                        do {
                            bc_next(lookahead, mod, nextOp, nextOperand, nextPos);
                            while (nextOp == Pyc::CACHE && !lookahead.atEof())
                                bc_next(lookahead, mod, nextOp, nextOperand, nextPos);
                        } while (cleanupOps++ < 3 && !lookahead.atEof()
                                 && (nextOp == Pyc::LOAD_CONST_A || nextOp == Pyc::LOAD_COMMON_CONSTANT_A
                                     || nextOp == Pyc::STORE_FAST_A
                                     || nextOp == Pyc::STORE_NAME_A || nextOp == Pyc::STORE_DEREF_A
                                     || nextOp == Pyc::DELETE_FAST_A || nextOp == Pyc::DELETE_NAME_A
                                     || nextOp == Pyc::DELETE_DEREF_A));
                        if (nextOp == Pyc::RETURN_VALUE
                                || nextOp == Pyc::INSTRUMENTED_RETURN_VALUE_A)
                            break;
                    }
                } else {
                    cleanBuild = false;
                }
            }
            if (mod->verCompare(3, 11) >= 0) {
                int loops = 0;
                std::stack<PycRef<ASTBlock> > pending = blocks;
                while (!pending.empty()) {
                    if (pending.top()->blktype() == ASTBlock::BLK_FOR
                            || pending.top()->blktype() == ASTBlock::BLK_ASYNCFOR)
                        loops++;
                    pending.pop();
                }
                // return inside loops: (SWAP 2; POP_TOP)+ RETURN_VALUE drops each hidden iterator (3.15: SWAP 3 + POP_TOP pair)
                int swapArg = mod->verCompare(3, 15) >= 0 ? 3 : 2;
                int pops = swapArg - 1, iters = 0, at = curpos, retAt = -1;
                int op = 0, arg = 0, next = 0;
                while (loops > 0 && operand == swapArg) {
                    bool chain = ast_read_wordcode_instr(code->code(), mod, at, op, arg, next)
                            && op == Pyc::SWAP_A && arg == swapArg;
                    at = next;
                    for (int i = 0; chain && i < pops; i++) {
                        while ((chain = ast_read_wordcode_instr(code->code(), mod, at, op, arg, next)) && op == Pyc::CACHE)
                            at = next;
                        chain = chain && op == Pyc::POP_TOP;
                        at = next;
                    }
                    if (!chain)
                        break;
                    iters++;
                    while (ast_read_wordcode_instr(code->code(), mod, at, op, arg, next) && op == Pyc::CACHE)
                        at = next;
                    if (op == Pyc::RETURN_VALUE || op == Pyc::INSTRUMENTED_RETURN_VALUE_A) {
                        retAt = at;
                        break;
                    }
                    if (op != Pyc::SWAP_A || iters >= loops)
                        break;
                }
                // Pre-3.12 FOR_ITER keeps no iterator node on the AST stack
                int dropIters = mod->verCompare(3, 12) >= 0 ? iters : 0;
                if (retAt > 0 && stack.size() > dropIters) {
                    PycRef<ASTNode> value = stack.top();
                    stack.pop();
                    for (int i = 0; i < dropIters; i++)
                        stack.pop();
                    stack.push(value);
                    while (pos < retAt && !source.atEof()) {
                        curpos = pos;
                        bc_next(source, mod, opcode, operand, pos);
                    }
                    break;
                }
            }
            if (!stack.swap(operand)) {
                fprintf(stderr, "Warning: invalid SWAP operand %d at offset %d\n", operand, pos);
                cleanBuild = false;
            }
            break;
        case Pyc::BINARY_SLICE:
            {
                PycRef<ASTNode> end = stack.top();
                stack.pop();
                PycRef<ASTNode> start = stack.top();
                stack.pop();
                PycRef<ASTNode> dest = stack.top();
                stack.pop();

                if (start.type() == ASTNode::NODE_OBJECT
                        && start.cast<ASTObject>()->object() == Pyc_None) {
                    start = NULL;
                }

                if (end.type() == ASTNode::NODE_OBJECT
                        && end.cast<ASTObject>()->object() == Pyc_None) {
                    end = NULL;
                }

                PycRef<ASTNode> slice;
                if (start == NULL && end == NULL) {
                    slice = new ASTSlice(ASTSlice::SLICE0);
                } else if (start == NULL) {
                    slice = new ASTSlice(ASTSlice::SLICE2, start, end);
                } else if (end == NULL) {
                    slice = new ASTSlice(ASTSlice::SLICE1, start, end);
                } else {
                    slice = new ASTSlice(ASTSlice::SLICE3, start, end);
                }
                stack.push(new ASTSubscr(dest, slice));
            }
            break;
        case Pyc::STORE_SLICE:
            {
                PycRef<ASTNode> end = stack.top();
                stack.pop();
                PycRef<ASTNode> start = stack.top();
                stack.pop();
                PycRef<ASTNode> dest = stack.top();
                stack.pop();
                PycRef<ASTNode> values = stack.top();
                stack.pop();

                if (start.type() == ASTNode::NODE_OBJECT
                        && start.cast<ASTObject>()->object() == Pyc_None) {
                    start = NULL;
                }

                if (end.type() == ASTNode::NODE_OBJECT
                        && end.cast<ASTObject>()->object() == Pyc_None) {
                    end = NULL;
                }

                PycRef<ASTNode> slice;
                if (start == NULL && end == NULL) {
                    slice = new ASTSlice(ASTSlice::SLICE0);
                } else if (start == NULL) {
                    slice = new ASTSlice(ASTSlice::SLICE2, start, end);
                } else if (end == NULL) {
                    slice = new ASTSlice(ASTSlice::SLICE1, start, end);
                } else {
                    slice = new ASTSlice(ASTSlice::SLICE3, start, end);
                }

                curblock->append(new ASTStore(values, new ASTSubscr(dest, slice)));
            }
            break;
        case Pyc::COPY_A:
            {
                PycRef<ASTNode> value = stack.top(operand);
                // Only COPY 1 is an assignment duplicate. COPY 2/3 moves exception state.
                if (operand == 1)
                    stack.push(value, curpos);
                else
                    stack.push(value);
            }
            break;
        case Pyc::EXTENDED_ARG_A:
            break;
        case Pyc::SEND_A:
            {
                // await / yield from: the forward target is where the result is used; the yield loop is not source
                if (stack.empty()) {
                    cleanBuild = false;
                    break;
                }
                stack.pop();
                if (mod->verCompare(3, 15) >= 0 && !stack.empty() && stack.top() == nullptr)
                    stack.pop();
                int target = ast_relative_jump_target(mod, opcode, operand, pos, false);
                while (pos < target && !source.atEof()) {
                    curpos = pos;
                    bc_next(source, mod, opcode, operand, pos);
                }
                if (mod->verCompare(3, 12) >= 0 && code->code() != nullptr) {
                    int op = 0, arg = 0, next = 0;
                    if (ast_read_wordcode_instr(code->code(), mod, pos, op, arg, next)
                            && (op == Pyc::END_SEND || op == Pyc::INSTRUMENTED_END_SEND_A)) {
                        curpos = pos;
                        bc_next(source, mod, opcode, operand, pos);
                    }
                }
            }
            break;
        case Pyc::END_SEND:
        case Pyc::INSTRUMENTED_END_SEND_A:
            // Consumed with SEND when it is the result edge. A lone one keeps the awaited value.
            break;
        case Pyc::CLEANUP_THROW:
            {
                // Exception edge of SEND: CLEANUP_THROW; jump back to END_SEND; StopIteration wrapper
                int op = 0, arg = 0, next = 0;
                if (code->code() != nullptr
                        && ast_read_wordcode_instr(code->code(), mod, pos, op, arg, next)
                        && (op == Pyc::JUMP_BACKWARD_A || op == Pyc::JUMP_BACKWARD_NO_INTERRUPT_A
                            || op == Pyc::INSTRUMENTED_JUMP_BACKWARD_A)) {
                    curpos = pos;
                    bc_next(source, mod, opcode, operand, pos);
                    if (ast_read_wordcode_instr(code->code(), mod, pos, op, arg, next)
                            && op == Pyc::CALL_INTRINSIC_1_A) {
                        curpos = pos;
                        bc_next(source, mod, opcode, operand, pos);
                        if (ast_read_wordcode_instr(code->code(), mod, pos, op, arg, next)
                                && (op == Pyc::RERAISE || op == Pyc::RERAISE_A)) {
                            curpos = pos;
                            bc_next(source, mod, opcode, operand, pos);
                        }
                    }
                }
            }
            break;
        case Pyc::ASYNC_GEN_WRAP:
            break;
        case Pyc::BEFORE_ASYNC_WITH:
            if (mod->verCompare(3, 11) < 0) {
                fprintf(stderr, "Unsupported opcode: %s (%d), emitting placeholder\n",
                        Pyc::OpcodeName(opcode), opcode);
                cleanBuild = false;
                curblock->append(new ASTUnsupported(std::string("# unsupported opcode ") +
                                 Pyc::OpcodeName(opcode)));
                break;
            }
            {
                auto it = withBodyEndByBefore.find(curpos);
                if (it != withBodyEndByBefore.end()) {
                    PycRef<ASTBlock> withblock = new ASTWithBlock(it->second);
                    blocks.push(withblock);
                    curblock = blocks.top();
                } else {
                    fprintf(stderr, "Warning: async with in %s could not be reconstructed (offset %d)\n",
                            code->name() != nullptr ? code->name()->value() : "<unknown>", curpos);
                    cleanBuild = false;
                }
            }
            break;
        default:
            {
                fprintf(stderr, "Unsupported opcode: %s (%d), emitting placeholder\n",
                        Pyc::OpcodeName(opcode), opcode);
                cleanBuild = false;
                curblock->append(new ASTUnsupported(std::string("# unsupported opcode ") +
                                 Pyc::OpcodeName(opcode)));
            }
            break;
        }

        // A return ends a re-opened loop fragment
        if (reopenedLoop != nullptr && curblock == reopenedLoop && blocks.size() > 1
                && (opcode == Pyc::RETURN_VALUE || opcode == Pyc::RETURN_CONST_A)) {
            blocks.pop();
            curblock = blocks.top();
            reopenedLoop = nullptr;
        }

        if (blocks.empty()) {
            cleanBuild = false;
            blocks.push(defblock);
            curblock = defblock;
        }

        else_pop =  ( (curblock->blktype() == ASTBlock::BLK_ELSE)
                      || (curblock->blktype() == ASTBlock::BLK_IF)
                      || (curblock->blktype() == ASTBlock::BLK_ELIF) )
                 && (curblock->end() == pos);
    }

    if (stack_hist.size()) {
        if (mod->verCompare(3, 14) < 0)
            fprintf(stderr, "Warning: Stack history is not empty in %s!\n",
                    code->name() != nullptr ? code->name()->value() : "<unknown>");

        while (stack_hist.size()) {
            stack_hist.pop();
        }
    }

    if (blocks.size() > 1) {
        if (mod->verCompare(3, 14) < 0)
            fprintf(stderr, "Warning: block stack is not empty in %s!\n",
                    code->name() != nullptr ? code->name()->value() : "<unknown>");

        while (blocks.size() > 1) {
            PycRef<ASTBlock> tmp = blocks.top();
            blocks.pop();

            if (tmp != reopenedLoop)
                blocks.top()->append(tmp.cast<ASTNode>());
        }
    }

    if (mod->verCompare(3, 11) >= 0)
        defblock->removeCompilerArtifacts();
    if (mod->verCompare(3, 14) >= 0)
        defblock->pruneUnreachableAfterReturn();
    return new ASTNodeList(defblock->nodes());
}

// COPY 1 / DUP_TOP leaves the same node under the stored value. Keep one named expression.
// DUP_TOP leaves the original under the named expression. A following store keeps it; anything else must not evaluate it again.
static void ast_drop_named_dup(FastStack& stack, PycRef<PycCode> code, PycModule* mod, int pos)
{
    if (mod->verCompare(3, 8) < 0 || code == nullptr || code->code() == nullptr
            || stack.empty() || stack.top() == nullptr
            || stack.top().type() != ASTNode::NODE_CHAINSTORE)
        return;
    PycRef<ASTChainStore> chain = stack.top().cast<ASTChainStore>();
    if (!chain->expression() || chain->nodes().size() != 1)
        return;
    int op = 0, arg = 0, next = 0;
    if (!ast_read_wordcode_instr(code->code(), mod, pos, op, arg, next))
        return;
    if (op == Pyc::STORE_FAST_A || op == Pyc::STORE_NAME_A || op == Pyc::STORE_GLOBAL_A
            || op == Pyc::STORE_DEREF_A || op == Pyc::STORE_ATTR_A)
        return;
    PycRef<ASTNode> top = stack.top();
    stack.pop();
    PycRef<ASTNode> src = chain->src();
    for (int n = 0; src != nullptr && src.type() == ASTNode::NODE_CHAINSTORE && n < 8; n++)
        src = src.cast<ASTChainStore>()->src();
    if (!stack.empty() && stack.top() == src)
        stack.pop();
    stack.push(top);
}

// A duplicated value stored into a target stays one chain: o.x = b = g(), not two calls
static bool ast_keep_chain_target(PycRef<ASTNode> value, PycRef<ASTNode> target,
                                  FastStack& stack, PycModule* mod, bool wasDup)
{
    // An existing chain is extended by append_to_chain_store; wrapping it makes `a := 1`
    // wasDup is the DUP_TOP/COPY 1 mark captured before the store popped this value
    if (mod->verCompare(3, 8) < 0 || !wasDup || value == nullptr
            || value.type() == ASTNode::NODE_CHAINSTORE
            || stack.empty() || stack.top() != value)
        return false;
    stack.pop();
    ASTNodeList::list_t targets;
    PycRef<ASTChainStore> chain = new ASTChainStore(targets, value);
    chain->append(target);
    stack.push(chain.cast<ASTNode>());
    return true;
}

static bool ast_is_assign_store(int op)
{
    return op == Pyc::STORE_FAST_A || op == Pyc::STORE_NAME_A || op == Pyc::STORE_GLOBAL_A
            || op == Pyc::STORE_DEREF_A || op == Pyc::STORE_ATTR_A || op == Pyc::STORE_SUBSCR
            || op == Pyc::STORE_FAST_STORE_FAST_A || op == Pyc::STORE_FAST_LOAD_FAST_A;
}

// A bare STORE later in this run is one chain. COPY/DUP before every remaining store is nested :=.
static bool ast_chain_extended_by_later_store(PycRef<PycCode> code, PycModule* mod, int pos)
{
    if (code == nullptr || code->code() == nullptr)
        return false;
    int op = 0, arg = 0, next = 0, at = pos;
    for (int n = 0; n < 32; n++) {
        if (!ast_read_wordcode_instr(code->code(), mod, at, op, arg, next))
            return false;
        at = next;
        while (op == Pyc::CACHE) {
            if (!ast_read_wordcode_instr(code->code(), mod, at, op, arg, next))
                return false;
            at = next;
        }
        if (op == Pyc::DUP_TOP || (op == Pyc::COPY_A && arg == 1)) {
            if (!ast_read_wordcode_instr(code->code(), mod, at, op, arg, next))
                return false;
            at = next;
            while (op == Pyc::CACHE) {
                if (!ast_read_wordcode_instr(code->code(), mod, at, op, arg, next))
                    return false;
                at = next;
            }
            if (!ast_is_assign_store(op))
                return false;
            // STORE_FAST_STORE_FAST writes the last two targets and ends the chain
            if (op == Pyc::STORE_FAST_STORE_FAST_A)
                return true;
            continue;
        }
        return ast_is_assign_store(op);
    }
    return false;
}

static bool ast_store_named_expr(PycRef<ASTNode> value, PycRef<ASTNode> name,
                                 FastStack& stack, PycModule* mod, bool wasDup,
                                 PycRef<PycCode> code, int pos)
{
    // A leftover null is not a copy of None. Only a recorded DUP_TOP or COPY 1 is.
    if (mod->verCompare(3, 8) < 0 || !wasDup || stack.empty() || stack.top() != value)
        return false;
    if (value != nullptr && value.type() == ASTNode::NODE_CHAINSTORE) {
        if (ast_chain_extended_by_later_store(code, mod, pos)) {
            value.cast<ASTChainStore>()->append(name);
            return true;
        }
        stack.pop();
        ASTNodeList::list_t targets;
        PycRef<ASTChainStore> named = new ASTChainStore(targets, value);
        named->append(name);
        named->setExpression(true);
        stack.push(named.cast<ASTNode>());
        return true;
    }
    // LOAD_CONST None is a null stack slot; two of them are still one None
    if (value == nullptr)
        value = new ASTObject(Pyc_None);
    stack.pop();
    ASTNodeList::list_t targets;
    PycRef<ASTChainStore> named = new ASTChainStore(targets, value);
    named->append(name);
    named->setExpression(true);
    stack.push(named.cast<ASTNode>());
    return true;
}

static void append_to_chain_store(const PycRef<ASTNode> &chainStore,
        PycRef<ASTNode> item, FastStack& stack, const PycRef<ASTBlock>& curblock)
{
    stack.pop();    // ignore identical source object.
    chainStore.cast<ASTChainStore>()->append(item);
    // No value left under the targets: this is a statement. A remaining value is named-expr context.
    PycRef<ASTNode> under = stack.top();
    if (under == nullptr || under.type() == PycObject::TYPE_NULL) {
        curblock->append(chainStore);
    } else {
        chainStore.cast<ASTChainStore>()->setExpression(true);
        stack.push(chainStore);
    }
}

// `import a.b` binds `a`; any other target, or an IMPORT_FROM walk, needs `as name`
static void print_module_import(PycRef<ASTImport> import, PycRef<ASTNode> dest, PycModule* mod,
                                std::ostream& pyc_output)
{
    pyc_output << "import ";
    print_src(import->name(), mod, pyc_output);
    PycRef<ASTName> module = import->name().try_cast<ASTName>();
    PycRef<ASTName> target = dest.try_cast<ASTName>();
    if (module == nullptr || target == nullptr)
        return;
    std::string full = module->name()->strValue();
    if (import->moduleAlias() || target->name()->strValue() != full.substr(0, full.find('.'))) {
        pyc_output << " as ";
        print_src(dest, mod, pyc_output);
    }
}

static bool ast_is_return_none(PycRef<ASTNode> node)
{
    PycRef<ASTReturn> ret = node.try_cast<ASTReturn>();
    if (ret == nullptr || ret->rettype() != ASTReturn::RETURN)
        return false;
    PycRef<ASTObject> obj = ret->value().try_cast<ASTObject>();
    return ret->value() == nullptr || (obj != nullptr && obj->object().type() == PycObject::TYPE_NONE);
}

// 3.11+ copies the function's implicit `return None` to the end of a trailing try body (and its trailing if/else chain)
template <class Body>
static void ast_strip_tail_return_none(PycRef<Body> blk, bool insideTry)
{
    if (blk == nullptr || blk->nodes().empty())
        return;
    PycRef<ASTNode> last = blk->nodes().back();
    if (insideTry && ast_is_return_none(last) && blk->nodes().size() > 1) {
        blk->removeLast();
        return;
    }
    PycRef<ASTBlock> tail = last.try_cast<ASTBlock>();
    if (tail == nullptr)
        return;
    if (tail->blktype() == ASTBlock::BLK_CONTAINER) {
        for (const auto& child : tail->nodes()) {
            PycRef<ASTBlock> cb = child.try_cast<ASTBlock>();
            if (cb != nullptr && cb->blktype() == ASTBlock::BLK_TRY)
                ast_strip_tail_return_none(cb, true);
        }
        return;
    }
    if (!insideTry)
        return;
    // Trailing if/elif/else chain inside the try body
    for (auto it = blk->nodes().rbegin(); it != blk->nodes().rend(); ++it) {
        PycRef<ASTNode> node = *it;
        PycRef<ASTBlock> b = node.try_cast<ASTBlock>();
        if (b == nullptr || (b->blktype() != ASTBlock::BLK_IF && b->blktype() != ASTBlock::BLK_ELIF
                    && b->blktype() != ASTBlock::BLK_ELSE))
            break;
        ast_strip_tail_return_none(b, true);
        if (b->blktype() == ASTBlock::BLK_IF)
            break;
    }
}

// 3.12+ compiles `if C: ...; break/return` as a jump-if-true over `continue`; a negated continue guard at such a loop-body tail is that if
// A continue/break right after break, continue, return or raise in the same block is a dead jump
template <class Body>
static void ast_drop_dead_jumps(PycRef<Body> body)
{
    if (body == nullptr)
        return;
    std::vector<PycRef<ASTNode> > nodes(body->nodes().begin(), body->nodes().end());
    std::vector<PycRef<ASTNode> > kept;
    bool afterExit = false;
    for (const auto& node : nodes) {
        PycRef<ASTKeyword> kw = node.try_cast<ASTKeyword>();
        bool jump = kw != nullptr && (kw->key() == ASTKeyword::KW_CONTINUE || kw->key() == ASTKeyword::KW_BREAK);
        if (jump && afterExit)
            continue;
        kept.push_back(node);
        afterExit = jump || node.type() == ASTNode::NODE_RETURN || node.type() == ASTNode::NODE_RAISE;
        PycRef<ASTBlock> blk = node.try_cast<ASTBlock>();
        if (blk != nullptr)
            ast_drop_dead_jumps(blk);
    }
    if (kept.size() == nodes.size())
        return;
    while (!body->nodes().empty())
        body->removeLast();
    for (const auto& node : kept)
        body->append(node);
}

template <class Body>
static void ast_fold_continue_guards(PycRef<Body> body, bool loopTail)
{
    for (const auto& n : body->nodes()) {
        PycRef<ASTNode> node = n;
        PycRef<ASTBlock> b = node.try_cast<ASTBlock>();
        if (b != nullptr)
            ast_fold_continue_guards(b, b->blktype() == ASTBlock::BLK_FOR || b->blktype() == ASTBlock::BLK_WHILE
                                         || b->blktype() == ASTBlock::BLK_ASYNCFOR);
    }
    if (!loopTail)
        return;
    std::vector<PycRef<ASTNode> > nodes(body->nodes().begin(), body->nodes().end());
    for (size_t i = 0; i + 1 < nodes.size(); i++) {
        PycRef<ASTCondBlock> guard = nodes[i].try_cast<ASTCondBlock>();
        if (guard == nullptr || guard->blktype() != ASTBlock::BLK_IF || guard->nodes().size() != 1
                || !guard->negative())
            continue;
        PycRef<ASTKeyword> kw = guard->nodes().front().try_cast<ASTKeyword>();
        if (kw == nullptr || kw->key() != ASTKeyword::KW_CONTINUE)
            continue;
        PycRef<ASTBlock> following = nodes[i + 1].try_cast<ASTBlock>();
        if (following != nullptr && (following->blktype() == ASTBlock::BLK_ELSE
                    || following->blktype() == ASTBlock::BLK_ELIF))
            continue;
        PycRef<ASTKeyword> lastKw = nodes.back().try_cast<ASTKeyword>();
        if (nodes.back().type() != ASTNode::NODE_RETURN
                && (lastKw == nullptr || lastKw->key() != ASTKeyword::KW_BREAK))
            continue;
        PycRef<ASTCondBlock> folded = new ASTCondBlock(ASTBlock::BLK_IF, guard->end(), guard->cond(),
                                                       !guard->negative());
        folded->init(guard->inited());
        for (size_t j = i + 1; j < nodes.size(); j++)
            folded->append(nodes[j]);
        while (body->nodes().size() > i)
            body->removeLast();
        body->append(folded.cast<ASTNode>());
        ast_fold_continue_guards(folded, true);
        break;
    }
}

static int cmp_prec(PycRef<ASTNode> parent, PycRef<ASTNode> child)
{
    /* Determine whether the parent has higher precedence than therefore
       child, so we don't flood the source code with extraneous parens.
       Else we'd have expressions like (((a + b) + c) + d) when therefore
       equivalent, a + b + c + d would suffice. */

    if (parent.type() == ASTNode::NODE_UNARY && parent.cast<ASTUnary>()->op() == ASTUnary::UN_NOT)
        return 1;   // Always parenthesize not(x)
    if (child.type() == ASTNode::NODE_BINARY) {
        PycRef<ASTBinary> binChild = child.cast<ASTBinary>();
        if (parent.type() == ASTNode::NODE_BINARY) {
            PycRef<ASTBinary> binParent = parent.cast<ASTBinary>();
            if (binParent->right() == child) {
                if (binParent->op() == ASTBinary::BIN_SUBTRACT &&
                    binChild->op() == ASTBinary::BIN_ADD)
                    return 1;
                else if (binParent->op() == ASTBinary::BIN_DIVIDE &&
                         binChild->op() == ASTBinary::BIN_MULTIPLY)
                    return 1;
            }
            return binChild->op() - binParent->op();
        }
        else if (parent.type() == ASTNode::NODE_COMPARE)
            return (binChild->op() == ASTBinary::BIN_LOG_AND ||
                    binChild->op() == ASTBinary::BIN_LOG_OR) ? 1 : -1;
        else if (parent.type() == ASTNode::NODE_UNARY)
            return (binChild->op() == ASTBinary::BIN_POWER) ? -1 : 1;
    } else if (child.type() == ASTNode::NODE_UNARY) {
        PycRef<ASTUnary> unChild = child.cast<ASTUnary>();
        if (parent.type() == ASTNode::NODE_BINARY) {
            PycRef<ASTBinary> binParent = parent.cast<ASTBinary>();
            if (binParent->op() == ASTBinary::BIN_LOG_AND ||
                binParent->op() == ASTBinary::BIN_LOG_OR)
                return -1;
            else if (unChild->op() == ASTUnary::UN_NOT)
                return 1;
            else if (binParent->op() == ASTBinary::BIN_POWER)
                return 1;
            else
                return -1;
        } else if (parent.type() == ASTNode::NODE_COMPARE) {
            return (unChild->op() == ASTUnary::UN_NOT) ? 1 : -1;
        } else if (parent.type() == ASTNode::NODE_UNARY) {
            return unChild->op() - parent.cast<ASTUnary>()->op();
        }
    } else if (child.type() == ASTNode::NODE_COMPARE) {
        PycRef<ASTCompare> cmpChild = child.cast<ASTCompare>();
        if (parent.type() == ASTNode::NODE_BINARY)
            return (parent.cast<ASTBinary>()->op() == ASTBinary::BIN_LOG_AND ||
                    parent.cast<ASTBinary>()->op() == ASTBinary::BIN_LOG_OR) ? -1 : 1;
        else if (parent.type() == ASTNode::NODE_COMPARE)
            return cmpChild->op() - parent.cast<ASTCompare>()->op();
        else if (parent.type() == ASTNode::NODE_UNARY)
            return (parent.cast<ASTUnary>()->op() == ASTUnary::UN_NOT) ? -1 : 1;
    }

    /* For normal nodes, don't parenthesize anything */
    return -1;
}

static bool ast_is_yield_expr(PycRef<ASTNode> node)
{
    if (node == nullptr)
        return false;
    if (node.type() == ASTNode::NODE_RETURN) {
        int kind = node.cast<ASTReturn>()->rettype();
        return kind == ASTReturn::YIELD || kind == ASTReturn::YIELD_FROM;
    }
    return node.type() == ASTNode::NODE_AWAITABLE && node.cast<ASTAwaitable>()->yieldFrom();
}

static bool ast_is_await_expr(PycRef<ASTNode> node)
{
    return node != nullptr && node.type() == ASTNode::NODE_AWAITABLE
            && !node.cast<ASTAwaitable>()->yieldFrom();
}

// Names, calls, attributes and subscripts are primaries; await's operand must be one
static bool ast_is_await_primary(PycRef<ASTNode> node)
{
    if (node == nullptr)
        return true;
    switch (node.type()) {
    case ASTNode::NODE_NAME:
    case ASTNode::NODE_OBJECT:
    case ASTNode::NODE_CALL:
    case ASTNode::NODE_SUBSCR:
    case ASTNode::NODE_SLICE:
    case ASTNode::NODE_TUPLE:
    case ASTNode::NODE_LIST:
    case ASTNode::NODE_SET:
    case ASTNode::NODE_MAP:
    case ASTNode::NODE_CONST_MAP:
        return true;
    case ASTNode::NODE_BINARY:
        return node.cast<ASTBinary>()->op() == ASTBinary::BIN_ATTR;
    default:
        return false;
    }
}

static void print_ordered(PycRef<ASTNode> parent, PycRef<ASTNode> child,
                          PycModule* mod, std::ostream& pyc_output)
{
    if (child.type() == ASTNode::NODE_BINARY ||
        child.type() == ASTNode::NODE_COMPARE) {
        if (cmp_prec(parent, child) > 0) {
            pyc_output << "(";
            print_src(child, mod, pyc_output);
            pyc_output << ")";
        } else {
            print_src(child, mod, pyc_output);
        }
    } else if (child.type() == ASTNode::NODE_UNARY) {
        if (cmp_prec(parent, child) > 0) {
            pyc_output << "(";
            print_src(child, mod, pyc_output);
            pyc_output << ")";
        } else {
            print_src(child, mod, pyc_output);
        }
    } else if (ast_is_yield_expr(child)) {
        // yield is only an expression inside parentheses, except as a whole assignment RHS
        pyc_output << "(";
        print_src(child, mod, pyc_output);
        pyc_output << ")";
    } else if (ast_is_await_expr(child) && parent.type() == ASTNode::NODE_UNARY) {
        pyc_output << "(";
        print_src(child, mod, pyc_output);
        pyc_output << ")";
    } else {
        print_src(child, mod, pyc_output);
    }
}

static void print_paren_expr(PycRef<ASTNode> node, PycModule* mod, std::ostream& pyc_output, bool paren)
{
    if (paren)
        pyc_output << "(";
    print_src(node, mod, pyc_output);
    if (paren)
        pyc_output << ")";
}

static const int MAX_PRINT_INDENT = 512;

static void start_line(int indent, std::ostream& pyc_output)
{
    if (inLambda)
        return;
    if (indent > MAX_PRINT_INDENT)
        indent = MAX_PRINT_INDENT;
    for (int i=0; i<indent; i++)
        pyc_output << "    ";
}

static void end_line(std::ostream& pyc_output)
{
    if (inLambda)
        return;
    pyc_output << "\n";
}

int cur_indent = -1;
static void print_block(PycRef<ASTBlock> blk, PycModule* mod,
                        std::ostream& pyc_output, bool skip_first = false)
{
    ASTBlock::list_t lines = blk->nodes();

    if (lines.size() == 0) {
        PycRef<ASTNode> pass = new ASTKeyword(ASTKeyword::KW_PASS);
        start_line(cur_indent, pyc_output);
        print_src(pass, mod, pyc_output);
    }

    for (auto ln = lines.cbegin(); ln != lines.cend();) {
        if (skip_first) {
            ++ln;
            skip_first = false;
            continue;
        }
        if ((*ln).cast<ASTNode>().type() != ASTNode::NODE_NODELIST) {
            start_line(cur_indent, pyc_output);
        }
        print_src(*ln, mod, pyc_output);
        if (++ln != lines.end()) {
            end_line(pyc_output);
        }
    }
}

void print_formatted_value(PycRef<ASTFormattedValue> formatted_value, PycModule* mod,
                           std::ostream& pyc_output)
{
    pyc_output << "{";
    print_src(formatted_value->val(), mod, pyc_output);

    switch (formatted_value->conversion() & ASTFormattedValue::CONVERSION_MASK) {
    case ASTFormattedValue::NONE:
        break;
    case ASTFormattedValue::STR:
        pyc_output << "!s";
        break;
    case ASTFormattedValue::REPR:
        pyc_output << "!r";
        break;
    case ASTFormattedValue::ASCII:
        pyc_output << "!a";
        break;
    }
    if (formatted_value->conversion() & ASTFormattedValue::HAVE_FMT_SPEC) {
        pyc_output << ":";
        PycRef<ASTNode> format_spec = formatted_value->format_spec();
        PycRef<PycString> spec_string = format_spec != nullptr
                && format_spec.type() == ASTNode::NODE_OBJECT
                ? format_spec.cast<ASTObject>()->object().try_cast<PycString>() : nullptr;
        if (spec_string != nullptr) {
            pyc_output << spec_string->value();
        } else if (format_spec != nullptr) {
            print_src(format_spec, mod, pyc_output);
            cleanBuild = false;
        } else {
            cleanBuild = false;
        }
    }
    pyc_output << "}";
}

static std::unordered_set<ASTNode *> node_seen;

void print_src(PycRef<ASTNode> node, PycModule* mod, std::ostream& pyc_output)
{
    if (node == NULL) {
        pyc_output << "None";
        cleanBuild = true;
        return;
    }

    if (node_seen.find((ASTNode *)node) != node_seen.end()) {
        fputs("WARNING: Circular reference detected\n", stderr);
        return;
    }
    node_seen.insert((ASTNode *)node);

    switch (node->type()) {
    case ASTNode::NODE_BINARY:
    case ASTNode::NODE_COMPARE:
        {
            PycRef<ASTBinary> bin = node.cast<ASTBinary>();
            PycRef<ASTCompare> cmp = node.try_cast<ASTCompare>();
            bool parenLeft = ast_is_yield_expr(bin->left())
                    || (ast_is_await_expr(bin->left())
                        && (bin->op() == ASTBinary::BIN_ATTR || bin->op() == ASTBinary::BIN_POWER));
            if (cmp != nullptr && cmp->chained())
                print_paren_expr(bin->left(), mod, pyc_output, parenLeft);
            else if (parenLeft)
                print_paren_expr(bin->left(), mod, pyc_output, true);
            else
                print_ordered(node, bin->left(), mod, pyc_output);
            pyc_output << bin->op_str();
            print_ordered(node, bin->right(), mod, pyc_output);
        }
        break;
    case ASTNode::NODE_UNARY:
        {
            PycRef<ASTUnary> un = node.cast<ASTUnary>();
            pyc_output << un->op_str();
            if (un->op() == ASTUnary::UN_STAR)
                print_src(un->operand(), mod, pyc_output);
            else
                print_ordered(node, un->operand(), mod, pyc_output);
        }
        break;
    case ASTNode::NODE_CALL:
        {
            PycRef<ASTCall> call = node.cast<ASTCall>();
            print_paren_expr(call->func(), mod, pyc_output,
                    ast_is_await_expr(call->func()) || ast_is_yield_expr(call->func()));
            pyc_output << "(";
            bool first = true;
            for (const auto& param : call->pparams()) {
                if (!first)
                    pyc_output << ", ";
                print_paren_expr(param, mod, pyc_output, ast_is_yield_expr(param));
                first = false;
            }
            for (const auto& param : call->kwparams()) {
                if (!first)
                    pyc_output << ", ";
                if (param.first == nullptr) {
                    pyc_output << "**";
                } else if (param.first.type() == ASTNode::NODE_NAME) {
                    pyc_output << param.first.cast<ASTName>()->name()->value() << " = ";
                } else {
                    PycRef<PycString> str_name = param.first.cast<ASTObject>()->object().cast<PycString>();
                    pyc_output << str_name->value() << " = ";
                }
                print_src(param.second, mod, pyc_output);
                first = false;
            }
            if (call->hasVar()) {
                if (!first)
                    pyc_output << ", ";
                pyc_output << "*";
                print_src(call->var(), mod, pyc_output);
                first = false;
            }
            if (call->hasKW()) {
                if (!first)
                    pyc_output << ", ";
                pyc_output << "**";
                print_src(call->kw(), mod, pyc_output);
                first = false;
            }
            pyc_output << ")";
        }
        break;
    case ASTNode::NODE_DELETE:
        {
            pyc_output << "del ";
            print_src(node.cast<ASTDelete>()->value(), mod, pyc_output);
        }
        break;
    case ASTNode::NODE_EXEC:
        {
            PycRef<ASTExec> exec = node.cast<ASTExec>();
            pyc_output << "exec ";
            print_src(exec->statement(), mod, pyc_output);

            if (exec->globals() != NULL) {
                pyc_output << " in ";
                print_src(exec->globals(), mod, pyc_output);

                if (exec->locals() != NULL
                        && exec->globals() != exec->locals()) {
                    pyc_output << ", ";
                    print_src(exec->locals(), mod, pyc_output);
                }
            }
        }
        break;
    case ASTNode::NODE_FORMATTEDVALUE:
        pyc_output << "f" F_STRING_QUOTE;
        print_formatted_value(node.cast<ASTFormattedValue>(), mod, pyc_output);
        pyc_output << F_STRING_QUOTE;
        break;
    case ASTNode::NODE_JOINEDSTR:
        pyc_output << "f" F_STRING_QUOTE;
        for (const auto& val : node.cast<ASTJoinedStr>()->values()) {
            switch (val.type()) {
            case ASTNode::NODE_FORMATTEDVALUE:
                print_formatted_value(val.cast<ASTFormattedValue>(), mod, pyc_output);
                break;
            case ASTNode::NODE_OBJECT:
                // When printing a piece of the f-string, keep the quote style consistent.
                // This avoids problems when ''' or """ is part of the string.
                print_const(pyc_output, val.cast<ASTObject>()->object(), mod, F_STRING_QUOTE);
                break;
            default:
                print_src(val, mod, pyc_output);
                break;
            }
        }
        pyc_output << F_STRING_QUOTE;
        break;
    case ASTNode::NODE_KEYWORD:
        pyc_output << node.cast<ASTKeyword>()->word_str();
        break;
    case ASTNode::NODE_LIST:
        {
            pyc_output << "[";
            bool first = true;
            cur_indent++;
            for (const auto& val : node.cast<ASTList>()->values()) {
                if (first)
                    pyc_output << "\n";
                else
                    pyc_output << ",\n";
                start_line(cur_indent, pyc_output);
                print_src(val, mod, pyc_output);
                first = false;
            }
            cur_indent--;
            pyc_output << "]";
        }
        break;
    case ASTNode::NODE_SET:
        {
            pyc_output << "{";
            bool first = true;
            cur_indent++;
            for (const auto& val : node.cast<ASTSet>()->values()) {
                if (first)
                    pyc_output << "\n";
                else
                    pyc_output << ",\n";
                start_line(cur_indent, pyc_output);
                print_src(val, mod, pyc_output);
                first = false;
            }
            cur_indent--;
            pyc_output << "}";
        }
        break;
    case ASTNode::NODE_COMPREHENSION:
        {
            PycRef<ASTComprehension> comp = node.cast<ASTComprehension>();
            bool is_dict = comp->result() != NULL
                    && comp->result().type() == ASTNode::NODE_MAP;
            // A single-element set result marks a set comprehension
            bool is_set = comp->result() != NULL && comp->result().type() == ASTNode::NODE_SET
                    && comp->result().cast<ASTSet>()->values().size() == 1;
            bool is_generator = comp->isGeneratorExpr();

            pyc_output << (is_dict || is_set ? "{ " : (is_generator ? "( " : "[ "));
            if (is_set) {
                print_src(comp->result().cast<ASTSet>()->values().front(), mod, pyc_output);
            } else if (is_dict) {
                const auto& entries = comp->result().cast<ASTMap>()->values();
                if (!entries.empty()) {
                    print_src(entries.front().first, mod, pyc_output);
                    pyc_output << ": ";
                    print_src(entries.front().second, mod, pyc_output);
                }
            } else {
                print_src(comp->result(), mod, pyc_output);
            }

            for (const auto& gen : comp->generators()) {
                pyc_output << (gen->blktype() == ASTBlock::BLK_ASYNCFOR ? " async for " : " for ");
                print_src(gen->index(), mod, pyc_output);
                pyc_output << " in ";
                print_src(gen->iter(), mod, pyc_output);
                if (gen->condition()) {
                    pyc_output << " if ";
                    print_src(gen->condition(), mod, pyc_output);
                }
            }
            pyc_output << (is_dict || is_set ? " }" : (is_generator ? " )" : " ]"));
        }
        break;
    case ASTNode::NODE_MAP:
        {
            pyc_output << "{";
            bool first = true;
            cur_indent++;
            for (const auto& val : node.cast<ASTMap>()->values()) {
                if (first)
                    pyc_output << "\n";
                else
                    pyc_output << ",\n";
                start_line(cur_indent, pyc_output);
                if (val.first == NULL) {
                    /* Dictionary unpacking: {**expr} */
                    pyc_output << "**";
                    print_src(val.second, mod, pyc_output);
                } else {
                    print_src(val.first, mod, pyc_output);
                    pyc_output << ": ";
                    print_src(val.second, mod, pyc_output);
                }
                first = false;
            }
            cur_indent--;
            pyc_output << " }";
        }
        break;
    case ASTNode::NODE_CONST_MAP:
        {
            PycRef<ASTConstMap> const_map = node.cast<ASTConstMap>();
            PycTuple::value_t keys = const_map->keys().cast<ASTObject>()->object().cast<PycTuple>()->values();
            ASTConstMap::values_t values = const_map->values();

            auto map = new ASTMap;
            for (const auto& key : keys) {
                // Values are pushed onto the stack in reverse order.
                PycRef<ASTNode> value = values.back();
                values.pop_back();

                map->add(new ASTObject(key), value);
            }

            print_src(map, mod, pyc_output);
        }
        break;
    case ASTNode::NODE_NAME:
        pyc_output << unmangle_name(node.cast<ASTName>()->name()->value());
        break;
    case ASTNode::NODE_NODELIST:
        {
            cur_indent++;
            for (const auto& ln : node.cast<ASTNodeList>()->nodes()) {
                if (ln.cast<ASTNode>().type() != ASTNode::NODE_NODELIST) {
                    start_line(cur_indent, pyc_output);
                }
                print_src(ln, mod, pyc_output);
                end_line(pyc_output);
            }
            cur_indent--;
        }
        break;
    case ASTNode::NODE_BLOCK:
        {
            PycRef<ASTBlock> blk = node.cast<ASTBlock>();
            bool skip_first = false;
            if (blk->blktype() == ASTBlock::BLK_ELSE && blk->size() == 0)
                break;
            // Provisional 3.11+ except clause that no handler code ever reached
            if (blk->blktype() == ASTBlock::BLK_EXCEPT && blk->size() == 0 && blk->processed()
                    && blk.cast<ASTCondBlock>()->cond() == nullptr)
                break;

            if (cur_indent > MAX_PRINT_INDENT) {
                cleanBuild = false;
                pyc_output << "# unsupported deeply nested block";
                break;
            }

            if (blk->blktype() == ASTBlock::BLK_CONTAINER) {
                // 3.10 inlines `else: return` before the handler, so else may sit ahead of except
                if (mod->verCompare(3, 10) == 0)
                    ast_py310_else_after_except(blk.cast<ASTContainerBlock>());
                end_line(pyc_output);
                print_block(blk, mod, pyc_output);
                end_line(pyc_output);
                break;
            }

            pyc_output << blk->type_str();
            if (blk->blktype() == ASTBlock::BLK_IF
                    || blk->blktype() == ASTBlock::BLK_ELIF
                    || blk->blktype() == ASTBlock::BLK_WHILE) {
                if (blk.cast<ASTCondBlock>()->negative())
                    pyc_output << " not ";
                else
                    pyc_output << " ";

                // A while loop without a test (SETUP_LOOP form) is `while True:`
                if (blk->blktype() == ASTBlock::BLK_WHILE && blk.cast<ASTCondBlock>()->cond() == nullptr)
                    pyc_output << "True";
                else
                    print_src(blk.cast<ASTCondBlock>()->cond(), mod, pyc_output);
            } else if (blk->blktype() == ASTBlock::BLK_FOR || blk->blktype() == ASTBlock::BLK_ASYNCFOR) {
                pyc_output << " ";
                print_src(blk.cast<ASTIterBlock>()->index(), mod, pyc_output);
                pyc_output << " in ";
                print_src(blk.cast<ASTIterBlock>()->iter(), mod, pyc_output);
            } else if (blk->blktype() == ASTBlock::BLK_EXCEPT &&
                    blk.cast<ASTCondBlock>()->cond() != NULL) {
                pyc_output << " ";
                print_src(blk.cast<ASTCondBlock>()->cond(), mod, pyc_output);
                PycRef<ASTNode> excVar = blk.cast<ASTCondBlock>()->exceptVar();
                if (excVar != NULL) {
                    pyc_output << " as ";
                    print_src(excVar, mod, pyc_output);
                }
            } else if (blk->blktype() == ASTBlock::BLK_WITH) {
                pyc_output << " ";
                print_src(blk.cast<ASTWithBlock>()->expr(), mod, pyc_output);
                PycRef<ASTNode> var = blk.try_cast<ASTWithBlock>()->var();
                if (var != NULL) {
                    pyc_output << " as ";
                    print_src(var, mod, pyc_output);
                }
            }
            pyc_output << ":\n";

            cur_indent++;
            print_block(blk, mod, pyc_output, skip_first);
            cur_indent--;
        }
        break;
    case ASTNode::NODE_OBJECT:
        {
            PycRef<PycObject> obj = node.cast<ASTObject>()->object();
            if (obj.type() == PycObject::TYPE_CODE) {
                PycRef<PycCode> code = obj.cast<PycCode>();
                decompyle(code, mod, pyc_output);
            } else {
                print_const(pyc_output, obj, mod);
            }
        }
        break;
    case ASTNode::NODE_PRINT:
        {
            pyc_output << "print ";
            bool first = true;
            if (node.cast<ASTPrint>()->stream() != nullptr) {
                pyc_output << ">>";
                print_src(node.cast<ASTPrint>()->stream(), mod, pyc_output);
                first = false;
            }

            for (const auto& val : node.cast<ASTPrint>()->values()) {
                if (!first)
                    pyc_output << ", ";
                print_src(val, mod, pyc_output);
                first = false;
            }
            if (!node.cast<ASTPrint>()->eol())
                pyc_output << ",";
        }
        break;
    case ASTNode::NODE_RAISE:
        {
            PycRef<ASTRaise> raise = node.cast<ASTRaise>();
            pyc_output << "raise";
            if (mod->verCompare(3, 0) >= 0) {
                /* Python 3: `raise`, `raise X`, or `raise X from Y`. */
                int i = 0;
                for (const auto& param : raise->params()) {
                    pyc_output << (i == 0 ? " " : " from ");
                    print_src(param, mod, pyc_output);
                    ++i;
                }
            } else {
                /* Python 2: `raise [X [, Y [, Z]]]`. */
                bool first = true;
                for (const auto& param : raise->params()) {
                    pyc_output << (first ? " " : ", ");
                    print_src(param, mod, pyc_output);
                    first = false;
                }
            }
        }
        break;
    case ASTNode::NODE_AWAITABLE:
        {
            PycRef<ASTNode> expr = node.cast<ASTAwaitable>()->expression();
            pyc_output << (node.cast<ASTAwaitable>()->yieldFrom() ? "yield from " : "await ");
            // await binds tighter than +/**/unary, so a non-primary operand needs parentheses
            print_paren_expr(expr, mod, pyc_output,
                    !node.cast<ASTAwaitable>()->yieldFrom() && !ast_is_await_primary(expr));
        }
        break;
    case ASTNode::NODE_RETURN:
        {
            PycRef<ASTReturn> ret = node.cast<ASTReturn>();
            PycRef<ASTNode> value = ret->value();
            if (!inLambda) {
                switch (ret->rettype()) {
                case ASTReturn::RETURN:
                    pyc_output << "return ";
                    break;
                case ASTReturn::YIELD:
                    pyc_output << "yield";
                    // Bare `yield` is YIELD_VALUE of None; printing the None changes the statement
                    if (value == nullptr
                            || (value.type() == ASTNode::NODE_OBJECT
                                && value.cast<ASTObject>()->object() != nullptr
                                && value.cast<ASTObject>()->object().type() == PycObject::TYPE_NONE)) {
                        value = nullptr;
                        break;
                    }
                    pyc_output << " ";
                    break;
                case ASTReturn::YIELD_FROM:
                    if (value.type() == ASTNode::NODE_AWAITABLE) {
                        pyc_output << "await ";
                        value = value.cast<ASTAwaitable>()->expression();
                    } else {
                        pyc_output << "yield from ";
                    }
                    break;
                }
            }
            if (value != nullptr)
                print_src(value, mod, pyc_output);
            else if (inLambda || node.cast<ASTReturn>()->rettype() == ASTReturn::RETURN)
                pyc_output << "None";
        }
        break;
    case ASTNode::NODE_SLICE:
        {
            PycRef<ASTSlice> slice = node.cast<ASTSlice>();

            if (slice->op() & ASTSlice::SLICE1) {
                print_src(slice->left(), mod, pyc_output);
            }
            pyc_output << ":";
            if (slice->op() & ASTSlice::SLICE2) {
                print_src(slice->right(), mod, pyc_output);
            }
        }
        break;
    case ASTNode::NODE_IMPORT:
        {
            PycRef<ASTImport> import = node.cast<ASTImport>();
            if (import->stores().size()) {
                ASTImport::list_t stores = import->stores();

                if (import->lazy())
                    pyc_output << "lazy ";
                pyc_output << "from ";
                for (int i = 0; i < import->level(); i++)
                    pyc_output << ".";
                if (import->name().type() == ASTNode::NODE_IMPORT)
                    print_src(import->name().cast<ASTImport>()->name(), mod, pyc_output);
                else
                    print_src(import->name(), mod, pyc_output);
                pyc_output << " import ";

                if (stores.size() == 1) {
                    auto src = stores.front()->src();
                    auto dest = stores.front()->dest();
                    print_src(src, mod, pyc_output);

                    if (src.cast<ASTName>()->name()->value() != dest.cast<ASTName>()->name()->value()) {
                        pyc_output << " as ";
                        print_src(dest, mod, pyc_output);
                    }
                } else {
                    bool first = true;
                    for (const auto& st : stores) {
                        if (!first)
                            pyc_output << ", ";
                        print_src(st->src(), mod, pyc_output);
                        first = false;

                        if (st->src().cast<ASTName>()->name()->value() != st->dest().cast<ASTName>()->name()->value()) {
                            pyc_output << " as ";
                            print_src(st->dest(), mod, pyc_output);
                        }
                    }
                }
            } else {
                if (import->lazy())
                    pyc_output << "lazy ";
                pyc_output << "import ";
                print_src(import->name(), mod, pyc_output);
            }
        }
        break;
    case ASTNode::NODE_FUNCTION:
        {
            /* Actual named functions are NODE_STORE with a name */
            pyc_output << "(lambda ";
            PycRef<ASTNode> code = node.cast<ASTFunction>()->code();
            PycRef<PycCode> code_src = code.cast<ASTObject>()->object().cast<PycCode>();
            ASTFunction::defarg_t defargs = node.cast<ASTFunction>()->defargs();
            ASTFunction::defarg_t kwdefargs = node.cast<ASTFunction>()->kwdefargs();
            auto da = defargs.cbegin();
            int narg = 0;
            for (int i=0; i<code_src->argCount(); i++) {
                if (narg)
                    pyc_output << ", ";
                pyc_output << unmangle_name(code_src->getLocal(narg++)->value());
                if ((code_src->argCount() - i) <= (int)defargs.size()) {
                    pyc_output << " = ";
                    print_src(*da++, mod, pyc_output);
                }
            }
            da = kwdefargs.cbegin();
            if (code_src->kwOnlyArgCount() != 0) {
                pyc_output << (narg == 0 ? "*" : ", *");
                for (int i = 0; i < code_src->argCount(); i++) {
                    pyc_output << ", ";
                    pyc_output << unmangle_name(code_src->getLocal(narg++)->value());
                    if ((code_src->kwOnlyArgCount() - i) <= (int)kwdefargs.size()) {
                        pyc_output << " = ";
                        print_src(*da++, mod, pyc_output);
                    }
                }
            }
            pyc_output << ": ";

            inLambda = true;
            /* A lambda compiled as `return x if cond else y` is represented
               as an IF block containing a return followed by a return. A
               lambda body cannot contain a statement-level `if`; render this
               exact shape as the equivalent conditional expression. */
            PycRef<ASTNodeList> lambdaSource = BuildFromCode(code_src, mod).try_cast<ASTNodeList>();
            bool printedTernary = false;
            if (lambdaSource != nullptr && lambdaSource->nodes().size() == 2) {
                auto it = lambdaSource->nodes().begin();
                PycRef<ASTCondBlock> ifBlock = (*it).try_cast<ASTCondBlock>();
                ++it;
                PycRef<ASTReturn> elseReturn = (*it).try_cast<ASTReturn>();
                if (ifBlock != nullptr && ifBlock->blktype() == ASTBlock::BLK_IF
                        && ifBlock->nodes().size() == 1 && elseReturn != nullptr) {
                    PycRef<ASTReturn> ifReturn =
                            ifBlock->nodes().front().try_cast<ASTReturn>();
                    if (ifReturn != nullptr && ifBlock->cond() != nullptr) {
                        print_src(ifReturn->value(), mod, pyc_output);
                        pyc_output << " if ";
                        if (ifBlock->negative())
                            pyc_output << "not ";
                        print_src(ifBlock->cond(), mod, pyc_output);
                        pyc_output << " else ";
                        print_src(elseReturn->value(), mod, pyc_output);
                        printedTernary = true;
                    }
                }
            }
            if (!printedTernary)
                print_src(code, mod, pyc_output);
            inLambda = false;

            pyc_output << ")";
        }
        break;
    case ASTNode::NODE_STORE:
        {
            PycRef<ASTNode> src = node.cast<ASTStore>()->src();
            PycRef<ASTNode> dest = node.cast<ASTStore>()->dest();
            if (src.type() == ASTNode::NODE_FUNCTION) {
                PycRef<ASTNode> code = src.cast<ASTFunction>()->code();
                PycRef<PycCode> code_src = code.cast<ASTObject>()->object().cast<PycCode>();
                bool isLambda = false;

                if (strcmp(code_src->name()->value(), "<lambda>") == 0) {
                    pyc_output << "\n";
                    start_line(cur_indent, pyc_output);
                    print_src(dest, mod, pyc_output);
                    pyc_output << " = lambda ";
                    isLambda = true;
                } else {
                    pyc_output << "\n";
                    for (const auto& decorator : src.cast<ASTFunction>()->decorators()) {
                        start_line(cur_indent, pyc_output);
                        pyc_output << "@";
                        print_src(decorator, mod, pyc_output);
                        pyc_output << "\n";
                    }
                    start_line(cur_indent, pyc_output);
                    if (code_src->flags() & (PycCode::CO_COROUTINE | PycCode::CO_ASYNC_GENERATOR))
                        pyc_output << "async ";
                    pyc_output << "def ";
                    print_src(dest, mod, pyc_output);
                    pyc_output << "(";
                }

                ASTFunction::defarg_t defargs = src.cast<ASTFunction>()->defargs();
                ASTFunction::defarg_t kwdefargs = src.cast<ASTFunction>()->kwdefargs();
                /* Python signature order is: positional-or-keyword, *args,
                   keyword-only, **kwargs. Local variables, however, are ordered
                   positional, keyword-only, *args, **kwargs, so index them
                   explicitly rather than sequentially. */
                const int argC = code_src->argCount();
                const int kwC = code_src->kwOnlyArgCount();
                const bool hasVarArgs = (code_src->flags() & PycCode::CO_VARARGS) != 0;
                const bool hasVarKw = (code_src->flags() & PycCode::CO_VARKEYWORDS) != 0;
                bool firstParam = true;
                auto da = defargs.cbegin();
                for (int i = 0; i < argC; ++i) {
                    if (!firstParam) pyc_output << ", ";
                    firstParam = false;
                    pyc_output << unmangle_name(code_src->getLocal(i)->value());
                    if ((argC - i) <= (int)defargs.size()) {
                        pyc_output << " = ";
                        print_src(*da++, mod, pyc_output);
                    }
                }
                if (hasVarArgs) {
                    if (!firstParam) pyc_output << ", ";
                    firstParam = false;
                    pyc_output << "*" << unmangle_name(code_src->getLocal(argC + kwC)->value());
                } else if (kwC != 0) {
                    if (!firstParam) pyc_output << ", ";
                    firstParam = false;
                    pyc_output << "*";
                }
                auto kda = kwdefargs.cbegin();
                for (int i = 0; i < kwC; ++i) {
                    if (!firstParam) pyc_output << ", ";
                    firstParam = false;
                    pyc_output << unmangle_name(code_src->getLocal(argC + i)->value());
                    if ((kwC - i) <= (int)kwdefargs.size()) {
                        pyc_output << " = ";
                        print_src(*kda++, mod, pyc_output);
                    }
                }
                if (hasVarKw) {
                    if (!firstParam) pyc_output << ", ";
                    firstParam = false;
                    pyc_output << "**"
                               << unmangle_name(code_src->getLocal(argC + kwC + (hasVarArgs ? 1 : 0))->value());
                }

                if (isLambda) {
                    pyc_output << ": ";
                } else {
                    pyc_output << "):\n";
                    printDocstringAndGlobals = true;
                }

                bool preLambda = inLambda;
                inLambda |= isLambda;

                print_src(code, mod, pyc_output);

                inLambda = preLambda;
            } else if (src.type() == ASTNode::NODE_CLASS) {
                pyc_output << "\n";
                for (const auto& decorator : src.cast<ASTClass>()->decorators()) {
                    start_line(cur_indent, pyc_output);
                    pyc_output << "@";
                    print_src(decorator, mod, pyc_output);
                    pyc_output << "\n";
                }
                start_line(cur_indent, pyc_output);
                pyc_output << "class ";
                print_src(dest, mod, pyc_output);
                PycRef<ASTNode> bases_node = src.cast<ASTClass>()->bases();
                PycRef<ASTTuple> bases = bases_node.try_cast<ASTTuple>();
                ASTCall::kwparam_t classKw;
                {
                    PycRef<ASTNode> classCall = src.cast<ASTClass>()->code();
                    if (classCall != NULL && classCall.type() == ASTNode::NODE_CALL)
                        classKw = classCall.cast<ASTCall>()->kwparams();
                }
                if (bases != nullptr && (bases->values().size() > 0 || !classKw.empty())) {
                    pyc_output << "(";
                    bool first = true;
                    for (const auto& val : bases->values()) {
                        if (!first)
                            pyc_output << ", ";
                        print_src(val, mod, pyc_output);
                        first = false;
                    }
                    for (const auto& kv : classKw) {
                        if (!first)
                            pyc_output << ", ";
                        if (kv.first == nullptr) {
                            pyc_output << "**";
                        } else if (kv.first.type() == ASTNode::NODE_NAME) {
                            pyc_output << kv.first.cast<ASTName>()->name()->value() << " = ";
                        } else {
                            pyc_output << kv.first.cast<ASTObject>()->object()
                                          .cast<PycString>()->value() << " = ";
                        }
                        print_src(kv.second, mod, pyc_output);
                        first = false;
                    }
                    pyc_output << "):\n";
                } else if (bases_node != nullptr && bases == nullptr) {
                    pyc_output << "(";
                    print_src(bases_node, mod, pyc_output);
                    pyc_output << "):\n";
                    cleanBuild = false;
                } else {
                    // Don't put parens if there are no base classes
                    pyc_output << ":\n";
                }
                printClassDocstring = true;
                PycRef<ASTCall> class_call = src.cast<ASTClass>()->code().try_cast<ASTCall>();
                PycRef<ASTFunction> class_func = nullptr;
                if (class_call != nullptr)
                    class_func = class_call->func().try_cast<ASTFunction>();

                if (class_func != nullptr) {
                    PycRef<PycCode> class_code = class_func->code().cast<ASTObject>()
                            ->object().try_cast<PycCode>();
                    classNameStack.push_back(class_code != nullptr
                            ? class_code->name()->strValue() : std::string());
                    print_src(class_func->code(), mod, pyc_output);
                    classNameStack.pop_back();
                } else {
                    cleanBuild = false;
                    start_line(cur_indent + 1, pyc_output);
                    pyc_output << "# unsupported class body";
                    end_line(pyc_output);
                    start_line(cur_indent + 1, pyc_output);
                    pyc_output << "pass";
                    end_line(pyc_output);
                }
            } else if (src.type() == ASTNode::NODE_IMPORT) {
                PycRef<ASTImport> import = src.cast<ASTImport>();
                if (import->lazy())
                    pyc_output << "lazy ";
                if (import->fromlist() != NULL) {
                    PycRef<PycObject> fromlist = import->fromlist().cast<ASTObject>()->object();
                    if (fromlist != Pyc_None) {
                        pyc_output << "from ";
                        for (int i = 0; i < import->level(); i++)
                            pyc_output << ".";
                        if (import->name().type() == ASTNode::NODE_IMPORT)
                            print_src(import->name().cast<ASTImport>()->name(), mod, pyc_output);
                        else
                            print_src(import->name(), mod, pyc_output);
                        pyc_output << " import ";
                        if (fromlist.type() == PycObject::TYPE_TUPLE ||
                                fromlist.type() == PycObject::TYPE_SMALL_TUPLE) {
                            bool first = true;
                            for (const auto& val : fromlist.cast<PycTuple>()->values()) {
                                if (!first)
                                    pyc_output << ", ";
                                pyc_output << val.cast<PycString>()->value();
                                first = false;
                            }
                        } else {
                            pyc_output << fromlist.cast<PycString>()->value();
                        }
                    } else {
                        print_module_import(import, dest, mod, pyc_output);
                    }
                } else {
                    print_module_import(import, dest, mod, pyc_output);
                }
            } else if (src.type() == ASTNode::NODE_BINARY
                    && src.cast<ASTBinary>()->is_inplace()) {
                print_src(src, mod, pyc_output);
            } else {
                print_src(dest, mod, pyc_output);
                pyc_output << " = ";
                print_src(src, mod, pyc_output);
            }
        }
        break;
    case ASTNode::NODE_CHAINSTORE:
        {
            PycRef<ASTChainStore> chain = node.cast<ASTChainStore>();
            // One target kept as a value is a named expression. Longer chains stay a = b = c.
            if (chain->expression() && chain->nodes().size() == 1 && mod->verCompare(3, 8) >= 0) {
                pyc_output << "(";
                print_src(chain->nodes().front(), mod, pyc_output);
                pyc_output << " := ";
                print_src(chain->src(), mod, pyc_output);
                pyc_output << ")";
                break;
            }
            for (auto& dest : chain->nodes()) {
                print_src(dest, mod, pyc_output);
                pyc_output << " = ";
            }
            print_src(chain->src(), mod, pyc_output);
        }
        break;
    case ASTNode::NODE_SUBSCR:
        {
            print_paren_expr(node.cast<ASTSubscr>()->name(), mod, pyc_output,
                    ast_is_await_expr(node.cast<ASTSubscr>()->name())
                    || ast_is_yield_expr(node.cast<ASTSubscr>()->name()));
            pyc_output << "[";
            print_paren_expr(node.cast<ASTSubscr>()->key(), mod, pyc_output,
                    ast_is_yield_expr(node.cast<ASTSubscr>()->key()));
            pyc_output << "]";
        }
        break;
    case ASTNode::NODE_CONVERT:
        {
            pyc_output << "`";
            print_src(node.cast<ASTConvert>()->name(), mod, pyc_output);
            pyc_output << "`";
        }
        break;
    case ASTNode::NODE_TUPLE:
        {
            PycRef<ASTTuple> tuple = node.cast<ASTTuple>();
            ASTTuple::value_t values = tuple->values();
            if (tuple->requireParens())
                pyc_output << "(";
            bool first = true;
            for (const auto& val : values) {
                if (!first)
                    pyc_output << ", ";
                print_src(val, mod, pyc_output);
                first = false;
            }
            if (values.size() == 1)
                pyc_output << ',';
            if (tuple->requireParens())
                pyc_output << ')';
        }
        break;
    case ASTNode::NODE_ANNOTATED_VAR:
        {
            PycRef<ASTAnnotatedVar> annotated_var = node.cast<ASTAnnotatedVar>();
            PycRef<ASTObject> name = annotated_var->name().cast<ASTObject>();
            PycRef<ASTNode> annotation = annotated_var->annotation();

            pyc_output << name->object().cast<PycString>()->value();
            pyc_output << ": ";
            print_src(annotation, mod, pyc_output);
        }
        break;
    case ASTNode::NODE_TERNARY:
        {
            /* parenthesis might be needed
             * 
             * when if-expr is part of numerical expression, ternary has the LOWEST precedence
             *     print(a + b if False else c)
             * output is c, not a+c (a+b is calculated first)
             * 
             * but, let's not add parenthesis - to keep the source as close to original as possible in most cases
             */
            PycRef<ASTTernary> ternary = node.cast<ASTTernary>();
            //pyc_output << "(";
            print_src(ternary->if_expr(), mod, pyc_output);
            const auto if_block = ternary->if_block().cast<ASTCondBlock>();
            pyc_output << " if ";
            if (if_block->negative())
                pyc_output << "not ";
            print_src(if_block->cond(), mod, pyc_output);
            pyc_output << " else ";
            print_src(ternary->else_expr(), mod, pyc_output);
            //pyc_output << ")";
        }
        break;
    case ASTNode::NODE_LOCALS:
        pyc_output << "locals()";
        break;
    case ASTNode::NODE_LOADBUILDCLASS:
        /* This node normally folds into ASTClass before printing. Keep a
           printable best-effort fallback for partially recovered classes. */
        pyc_output << "__build_class__";
        break;
    case ASTNode::NODE_UNSUPPORTED:
        pyc_output << node.cast<ASTUnsupported>()->text();
        break;
    default:
        pyc_output << "<NODE:" << node->type() << ">";
        fprintf(stderr, "Unsupported Node type: %d\n", node->type());
        cleanBuild = false;
        node_seen.erase((ASTNode *)node);
        return;
    }

    cleanBuild = true;
    node_seen.erase((ASTNode *)node);
}

bool print_docstring(PycRef<PycObject> obj, int indent, PycModule* mod,
                     std::ostream& pyc_output)
{
    // docstrings are translated from the bytecode __doc__ = 'string' to simply '''string'''
    auto doc = obj.try_cast<PycString>();
    if (doc != nullptr) {
        start_line(indent, pyc_output);
        doc->print(pyc_output, mod, true);
        pyc_output << "\n";
        return true;
    }
    return false;
}

static std::unordered_set<PycCode *> code_seen;

// A free variable that this code stores is a nonlocal; a read-only free var needs no declaration
static void ast_print_nonlocals(PycRef<PycCode> code, PycModule* mod, int indent, std::ostream& pyc_output)
{
    if (mod->verCompare(3, 0) < 0 || code == nullptr || code->code() == nullptr)
        return;
    // 3.11+ stores free-var names in localsplus; the kind byte 0x80 is CO_FAST_FREE
    std::set<int> freeIndex;
    std::set<std::string> frees;
    if (mod->verCompare(3, 11) >= 0 && code->localKinds() != nullptr
            && code->localKinds()->value() != nullptr) {
        const char* kinds = code->localKinds()->value();
        int n = code->localKinds()->length();
        for (int i = 0; i < n; i++) {
            if ((unsigned char)kinds[i] & 0x80)
                freeIndex.insert(i);
        }
    } else if (code->freeVars() != nullptr) {
        for (int i = 0; i < code->freeVars()->size(); i++) {
            PycRef<PycString> name = code->freeVars()->get(i).try_cast<PycString>();
            if (name != nullptr)
                frees.insert(name->value());
        }
    }
    if (freeIndex.empty() && frees.empty())
        return;
    std::vector<std::string> assigned;
    std::set<std::string> seen;
    PycBuffer src(code->code()->value(), code->code()->length());
    int op = 0, arg = 0, pos = 0;
    while (!src.atEof()) {
        bc_next(src, mod, op, arg, pos);
        if (op != Pyc::STORE_DEREF_A && op != Pyc::DELETE_DEREF_A)
            continue;
        PycRef<PycString> name;
        if (!freeIndex.empty()) {
            if (!freeIndex.count(arg))
                continue;
            name = code->getLocal(arg);
        } else {
            name = code->getCellVar(mod, arg);
        }
        if (name == nullptr)
            continue;
        std::string text = name->value();
        if (!frees.empty() && !frees.count(text))
            continue;
        if (!seen.insert(text).second)
            continue;
        assigned.push_back(text);
    }
    if (assigned.empty())
        return;
    start_line(indent, pyc_output);
    pyc_output << "nonlocal ";
    for (size_t i = 0; i < assigned.size(); i++) {
        if (i != 0)
            pyc_output << ", ";
        pyc_output << unmangle_name(assigned[i].c_str());
    }
    pyc_output << "\n";
}

/* A `return` is invalid at module scope, yet implicit returns can end up before
   linearly decoded exception-cleanup blocks as well as at the physical end.
   Strip every module return, recursively through module-level blocks. Only called on
   the <module> code object, whose blocks are module-level control flow (nested
   function/class bodies are separate code objects, so this never touches a real
   `return`). */
static void StripModuleReturns(PycRef<ASTNode> node)
{
    if (node == NULL)
        return;
    if (node.type() == ASTNode::NODE_NODELIST)
        node.cast<ASTNodeList>()->removeAllReturns();
    else if (node.type() == ASTNode::NODE_BLOCK)
        node.cast<ASTBlock>()->removeAllReturns();
}

void decompyle(PycRef<PycCode> code, PycModule* mod, std::ostream& pyc_output)
{
    if (code_seen.find((PycCode *)code) != code_seen.end()) {
        fputs("WARNING: Circular reference detected\n", stderr);
        return;
    }
    code_seen.insert((PycCode *)code);

    PycRef<ASTNode> source = BuildFromCode(code, mod);

    PycRef<ASTNodeList> clean = source.cast<ASTNodeList>();
    // Compiler epilogue of a generator is `return None`; a valued return is illegal in an async generator
    if (clean != nullptr && clean->nodes().size() != 0
            && (code->flags() & (PycCode::CO_GENERATOR | PycCode::CO_ASYNC_GENERATOR))
            && clean->nodes().back().type() == ASTNode::NODE_RETURN) {
        PycRef<ASTReturn> ret = clean->nodes().back().cast<ASTReturn>();
        PycRef<ASTObject> retObj = ret->value().try_cast<ASTObject>();
        if (ret->rettype() == ASTReturn::RETURN
                && (ret->value() == nullptr
                    || (retObj != nullptr && retObj->object().type() == PycObject::TYPE_NONE)))
            clean->removeLast();
    }
    if (cleanBuild && clean->nodes().size() != 0) {
        // The Python compiler adds some stuff that we don't really care
        // about, and would add extra code for re-compilation anyway.
        // We strip these lines out here, and then add a "pass" statement
        // if the cleaned up code is empty
        if (clean->nodes().size() != 0 && clean->nodes().front().type() == ASTNode::NODE_STORE) {
            PycRef<ASTStore> store = clean->nodes().front().cast<ASTStore>();
            if (store->src().type() == ASTNode::NODE_NAME
                    && store->dest().type() == ASTNode::NODE_NAME) {
                PycRef<ASTName> src = store->src().cast<ASTName>();
                PycRef<ASTName> dest = store->dest().cast<ASTName>();
                if (src->name()->isEqual("__name__")
                        && dest->name()->isEqual("__module__")) {
                    // __module__ = __name__
                    // Automatically added by Python 2.2.1 and later
                    clean->removeFirst();
                }
            }
        }
        if (clean->nodes().size() != 0 && clean->nodes().front().type() == ASTNode::NODE_STORE) {
            PycRef<ASTStore> store = clean->nodes().front().cast<ASTStore>();
            if (store->src().type() == ASTNode::NODE_OBJECT
                    && store->dest().type() == ASTNode::NODE_NAME) {
                PycRef<ASTObject> src = store->src().cast<ASTObject>();
                PycRef<PycString> srcString = src->object().try_cast<PycString>();
                PycRef<ASTName> dest = store->dest().cast<ASTName>();
                if (dest->name()->isEqual("__qualname__")) {
                    // __qualname__ = '<Class Name>'
                    // Automatically added by Python 3.3 and later
                    clean->removeFirst();
                }
            }
        }

        // Class and module docstrings may only appear at the beginning of their source
        if (printClassDocstring && clean->nodes().size() != 0
                && clean->nodes().front().type() == ASTNode::NODE_STORE) {
            PycRef<ASTStore> store = clean->nodes().front().cast<ASTStore>();
            if (store->dest().type() == ASTNode::NODE_NAME &&
                    store->dest().cast<ASTName>()->name()->isEqual("__doc__") &&
                    store->src().type() == ASTNode::NODE_OBJECT) {
                if (print_docstring(store->src().cast<ASTObject>()->object(),
                        cur_indent + (code->name()->isEqual("<module>") ? 0 : 1), mod, pyc_output))
                    clean->removeFirst();
            }
        }
        if (clean->nodes().size() != 0 && clean->nodes().back().type() == ASTNode::NODE_RETURN) {
            PycRef<ASTReturn> ret = clean->nodes().back().cast<ASTReturn>();

            PycRef<ASTObject> retObj = ret->value().try_cast<ASTObject>();
            if (ret->rettype() == ASTReturn::RETURN
                    && (ret->value() == NULL || ret->value().type() == ASTNode::NODE_LOCALS ||
                    (retObj && retObj->object().type() == PycObject::TYPE_NONE))) {
                clean->removeLast();  // Always an extraneous return statement
            }
        }
        if ((code->flags() & PycCode::CO_NEWLOCALS) && mod->verCompare(3, 11) >= 0)
            ast_strip_tail_return_none(clean, false);
        if (mod->verCompare(3, 12) >= 0)
            ast_fold_continue_guards(clean, false);
        ast_drop_dead_jumps(clean);

        // Strip compiler-generated __classcell__ store and return __class__ (3.6-3.10 fold them into one return)
        if (clean->nodes().size() &&
                clean->nodes().back().type() == ASTNode::NODE_RETURN) {
            PycRef<ASTReturn> ret = clean->nodes().back().cast<ASTReturn>();
            PycRef<ASTNode> retval = ret->value();
            if (retval != NULL && retval.type() == ASTNode::NODE_CHAINSTORE) {
                PycRef<ASTChainStore> chain = retval.cast<ASTChainStore>();
                PycRef<ASTName> dest = chain->nodes().size() == 1
                        ? chain->nodes().front().try_cast<ASTName>() : nullptr;
                if (dest != nullptr && dest->name()->isEqual("__classcell__"))
                    retval = chain->src();
            }
            if (retval != NULL && retval.type() == ASTNode::NODE_NAME &&
                    retval.cast<ASTName>()->name()->isEqual("__class__")) {
                clean->removeLast();
            }
        }
        if (clean->nodes().size() &&
                clean->nodes().back().type() == ASTNode::NODE_STORE) {
            PycRef<ASTStore> st = clean->nodes().back().cast<ASTStore>();
            if (st->dest().type() == ASTNode::NODE_NAME &&
                    st->dest().cast<ASTName>()->name()->isEqual("__classcell__")) {
                clean->removeLast();
            }
        }

        /* Strip the module's implicit trailing "return None" (invalid at
           module scope), even when nested in a trailing block. */
        if (code->name()->isEqual("<module>") && mod->verCompare(3, 11) >= 0)
            StripModuleReturns(clean.cast<ASTNode>());
        else if (code->name()->isEqual("<module>") && mod->verCompare(3, 0) >= 0) {
            // A return nested in a block is not legal at module scope. The module's own
            // trailing return is left in place; older tests compare that text.
            for (const auto& child : clean->nodes()) {
                if (child != nullptr && child.type() == ASTNode::NODE_BLOCK)
                    StripModuleReturns(child);
            }
        }
    }
    if (printClassDocstring)
        printClassDocstring = false;
    // This is outside the clean check so a source block will always
    // be compilable, even if decompylation failed.
    if (clean->nodes().size() == 0 && !code.isIdent(mod->code()))
        clean->append(new ASTKeyword(ASTKeyword::KW_PASS));

    bool part1clean = cleanBuild;

    if (printDocstringAndGlobals) {
        // 3.14+ only treats co_consts[0] as the docstring when CO_HAS_DOCSTRING is set
        bool hasDocstring = mod->verCompare(3, 14) < 0
                || (code->flags() & PycCode::CO_HAS_DOCSTRING) != 0;
        if (hasDocstring && code->consts()->size())
            print_docstring(code->getConst(0), cur_indent + 1, mod, pyc_output);

        PycCode::globals_t globs = code->getGlobals();
        if (globs.size()) {
            start_line(cur_indent + 1, pyc_output);
            pyc_output << "global ";
            bool first = true;
            for (const auto& glob : globs) {
                if (!first)
                    pyc_output << ", ";
                pyc_output << unmangle_name(glob->value());
                first = false;
            }
            pyc_output << "\n";
        }
        ast_print_nonlocals(code, mod, cur_indent + 1, pyc_output);
        printDocstringAndGlobals = false;
    }

    print_src(source, mod, pyc_output);

    if (!cleanBuild || !part1clean) {
        start_line(cur_indent, pyc_output);
        pyc_output << "# WARNING: Decompyle incomplete\n";
    }

    code_seen.erase((PycCode *)code);
}
