class ControlWindow:
    def __init__(self, metadata):
        self.metadata = metadata or {}
        self.build()

    def build(self):
        pass


def choose_duration(use_days):
    if use_days:
        value = 1
        unit = 2
        return (value, unit)
    value = 3
    unit = 4
    return (value, unit)


def retry_password(read_password, verify_password, limit):
    password_ok = False
    failed = 0
    while not password_ok:
        password = read_password()
        if password is None:
            return None
        if verify_password(password):
            password_ok = True
            continue
        failed += 1
        if failed < limit:
            continue
        return False
    return True


def monitor(clock, sleep, poll, deadline, expire):
    while clock() < deadline:
        sleep(2)
        if poll() is None:
            continue
        return None
    expire()


def refresh(metadata, now):
    """refresh expiry and trial"""
    expiry = metadata.get("expiry")
    if expiry:
        try:
            expired = now > int(expiry)
        except ValueError:
            expired = False
    trial = metadata.get("trial")
    return trial
