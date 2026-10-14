def drain_one(q):
    while q:
        q.pop()
    q.close()


def drain(queues):
    for q in queues:
        while q:
            q.pop()
        q.close()


def walk(rows):
    for row in rows:
        while row:
            if row.ok:
                return row
            row = row.next


def poll(source):
    while source.open:
        try:
            source.read()
        except IOError:
            source.reset()
