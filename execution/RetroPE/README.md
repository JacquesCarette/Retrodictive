# RetroPE

The code is in src/ and is meant to be built via `stack build`.

### profiling

(This assumes that `Main.hs` runs the things that need to be profiled)

To profile the code, 
```
stack build --profile
stack exec --profile RetroPE-exe -RTS -- +RTS -p
```
then look in `RetroPE-exe.prof` for the results.

