{
  inputs = {
    nixpkgs.url = "nixpkgs/nixos-25.05";
  };

  outputs = {self, nixpkgs}:
  let
    system = "x86_64-linux";
    pkgs = import nixpkgs { inherit system; };
    protocol-ladder = pkgs.callPackage ./default.nix {};
  in {
    checks.${system} = {
      inherit protocol-ladder;
    };
    devShells.${system}.default = pkgs.mkShell {
      packages = [
        pkgs.tamarin-prover
      ];
    };
  };
}
