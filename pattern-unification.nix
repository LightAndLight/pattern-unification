{ mkDerivation, base, bound, deriving-compat, lens, stdenv }:
mkDerivation {
  pname = "pattern-unification";
  version = "0.1.0.0";
  src = ./.;
  libraryHaskellDepends = [ base bound deriving-compat lens ];
  doHaddock = false;
  license = stdenv.lib.licenses.bsd3;
}
