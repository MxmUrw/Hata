# Hata

## Note
### Building
To build the `gi-cairo` bindings on windows, the following workaround is usually necessary:
https://github.com/haskell-gi/haskell-gi/wiki/Using-haskell-gi-in-Windows#a-workaround-for-stack


### Executing
To execute, on Windows we currently need to do:

```
SET PATH=C:\msys64\mingw64\bin;C:\msys64\usr\bin;%PATH%
SET PKG_CONFIG_PATH=C:\msys64\mingw64\lib\pkgconfig
SET XDG_DATA_DIRS=C:\msys64\mingw64\share
```

See https://github.com/haskell-gi/haskell-gi/wiki/Using-haskell-gi-in-Windows




