# cmdline

Программа прячет перый аргумент командой строки из /proc/PID/cmdline.
Используется `prctl` и флаг `PR_SET_MM`.

Компиляция:
```
make -s --always-make
```

**Needs work.**