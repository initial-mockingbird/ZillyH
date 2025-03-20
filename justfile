default: build



[group('build')]
[private]
_build_wasm o='./dist' package='WASM':
  ./build_scripts/build_wasm {{o}} {{package}}

[group('build')]
[private]
_build_main:
  cabal build Haskell-exe


[group('build')]
build wasm='1':
  hpack
  @bash -c {{if wasm == '1' {"\"just _build_wasm\""} else {"\"just _build_main\""} }}

[positional-arguments]
ghci *args='':
  hpack
  cabal repl {{args}}

clean:
  cabal clean
  rm -rf ./dist/**

