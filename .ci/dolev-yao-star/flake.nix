{
  inputs = {
    fstar-flake.url = "github:FStarLang/FStar";
    nixpkgs.follows = "fstar-flake/nixpkgs";

    comparse-flake = {
      url = "github:TWal/comparse";
      inputs.nixpkgs.follows = "nixpkgs";
      inputs.fstar-flake.follows = "fstar-flake";
    };

    dolev-yao-star-flake = {
      url = "github:REPROSEC/dolev-yao-star-extrinsic";
      inputs.nixpkgs.follows = "nixpkgs";
      inputs.fstar-flake.follows = "fstar-flake";
      inputs.comparse-flake.follows = "comparse-flake";
    };
  };

  outputs = {self, nixpkgs, fstar-flake, comparse-flake, dolev-yao-star-flake}:
  let
    system = "x86_64-linux";
    pkgs = import nixpkgs { inherit system; };
    z3 = fstar-flake.packages.${system}.z3;
    fstar = fstar-flake.packages.${system}.fstar;
    comparse = comparse-flake.packages.${system}.comparse;
    dolev-yao-star = dolev-yao-star-flake.packages.${system}.dolev-yao-star;
    protocol-ladder = pkgs.callPackage ./default.nix {inherit fstar z3 comparse dolev-yao-star;};
  in {
    checks.${system} = {
      inherit protocol-ladder;
    };
  };
}
