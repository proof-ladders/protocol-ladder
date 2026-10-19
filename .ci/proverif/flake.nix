{
  inputs = {
    nixpkgs.url = "nixpkgs/nixos-25.05";
  };

  outputs = {self, nixpkgs}:
  let
    system = "x86_64-linux";
    pkgs = import nixpkgs { inherit system; };
    proverif =
      pkgs.proverif.overrideDerivation (_: {
        patches = [ ./pv_div_by_zero_fix.diff ];
      })
    ;
    protocol-ladder = pkgs.callPackage ./default.nix { inherit proverif; };
  in {
    checks.${system} = {
      inherit protocol-ladder;
    };
    devShells.${system}.default = pkgs.mkShell {
      packages = [
        proverif
      ];
    };
  };
}
