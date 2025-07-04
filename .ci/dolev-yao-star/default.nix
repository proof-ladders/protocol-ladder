{lib, stdenv, which, fstar, z3, comparse, dolev-yao-star}:

stdenv.mkDerivation {
  name = "protocol-ladder";
  src = ./.;
  enableParallelBuilding = true;
  buildInputs = [ which fstar z3 ];
  COMPARSE_HOME = comparse;
  DY_HOME = dolev-yao-star;
  installPhase = ''
    mkdir -p $out
  '';
}
