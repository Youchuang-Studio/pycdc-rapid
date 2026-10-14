def read_password(getch):
    password = ''
    while True:
        char = getch()
        if char in ('\r', '\n'):
            print('')
            break
        if char == '\x08':
            if len(password) > 0:
                password = password[:-1]
                print('\x08 \x08')
        elif char == '\x03':
            raise KeyboardInterrupt
        else:
            password += char
    print(len(password))
    return password
