[English](../../README.markdown) | 中文

# pycdc-rapid

Python 字节码反汇编 / 反编译工具。

基于 Decompyle++ / pycdc：  
https://github.com/zrax/pycdc

Decompyle++ 旨在将编译后的 Python 字节码转换回有效、可读的 Python 源代码。

Decompyle++ 包含两个工具：

| 工具 | 说明 |
|---|---|
| `pycdas` | Python 字节码反汇编器 |
| `pycdc` | Python 字节码反编译器 |

## Release

预编译版本：

https://github.com/Youchuang-Studio/pycdc-rapid/releases

## 编译

使用 CMake 生成项目文件或 Makefile，然后编译生成的项目。

编译命令：

```bash
git clone https://github.com/Youchuang-Studio/pycdc-rapid.git
cd pycdc-rapid
mkdir build && cd build
cmake ..
cmake --build . --config Release
```

CMake 调试参数：

| 选项 | 说明 |
|---|---|
| `-DCMAKE_BUILD_TYPE=Debug` | 生成调试符号 |
| `-DENABLE_BLOCK_DEBUG=ON` | 启用 block 调试输出 |
| `-DENABLE_STACK_DEBUG=ON` | 启用 stack 调试输出 |

运行测试：

```bash
make check JOBS=4
```

只运行指定测试：

```bash
make check JOBS=4 FILTER=xxxx
```

## 使用

运行 `pycdas`，PYC 反汇编器：

```bash
./pycdas [PATH TO PYC FILE]
```

字节码反汇编结果会输出到 `stdout`。

运行 `pycdc`，PYC 反编译器：

```bash
./pycdc [PATH TO PYC FILE]
```

反编译得到的 Python 源代码会输出到 `stdout`，错误信息会输出到 `stderr`。

## Marshalled code objects

支持 Python marshalled code objects，例如：

```python
marshal.dumps(compile(...))
```

使用该功能时，需要在命令行指定：

```bash
-c -v <version>
```

因为 marshalled code object 本身不包含版本元数据。

示例：

```bash
./pycdas -c -v 3.14 example.marshal
./pycdc -c -v 3.14 example.marshal
```

## 参与贡献

Issue 与 PR 的提交要求请见[贡献指南](contributing.md)。

## 上游项目

本项目基于 Decompyle++ / pycdc：

https://github.com/zrax/pycdc

## 作者、许可与鸣谢

Decompyle++ 由 Michael Hansen 和 Darryl Pogue 开发。

其他贡献者：

| 贡献者 |
|---|
| charlietang98 |
| Kunal Parmar |
| Olivier Iffrig |
| Zlodiy |

## 许可证

GNU General Public License v3.0。

详情见 `LICENSE`。

## 哔哩哔哩

个人主页：[Tech悠悠](https://space.bilibili.com/1934537611)

## 赞赏

如果这个项目帮到了你，欢迎赞赏支持。

![赞赏码](../assets/sponsor-qr.jpg)

USDT-TRC20：<br>
[TRKeWXWc1GL7ARE1sX5rBDcYg9yStFsmnU](https://tronscan.org/#/address/TRKeWXWc1GL7ARE1sX5rBDcYg9yStFsmnU)

USDT-Solana：<br>
[BrKPdDdF8NY8k1f4A7RfN1inSDsxZ2d1atDHvGLjp23G](https://solscan.io/account/BrKPdDdF8NY8k1f4A7RfN1inSDsxZ2d1atDHvGLjp23G)
