{lib, stdenv, proverif}:

stdenv.mkDerivation {
  name = "protocol-ladder-proverif";
  src = ./.;
  enableParallelBuilding = false;
  buildInputs = [ proverif ];
  installPhase = ''
    mkdir -p $out
  '';
}
