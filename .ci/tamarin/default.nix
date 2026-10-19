{lib, stdenv, tamarin-prover}:

stdenv.mkDerivation {
  name = "protocol-ladder-tamarin";
  src = ./.;
  enableParallelBuilding = false;
  buildInputs = [ tamarin-prover ];
  LANG = "en_US.UTF-8";
  installPhase = ''
    mkdir -p $out
  '';
}
