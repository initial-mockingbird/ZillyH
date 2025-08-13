{
  inputs = {
    nixpkgs.url = "github:nixos/nixpkgs/nixpkgs-unstable";
    flake-parts.url = "github:hercules-ci/flake-parts";
    ghc-wasm.url = "gitlab:haskell-wasm/ghc-wasm-meta?host=gitlab.haskell.org";

  };
  outputs = inputs@{ self, nixpkgs, flake-parts, ... }:
    flake-parts.lib.mkFlake { inherit inputs; } {
      systems = nixpkgs.lib.systems.flakeExposed;
      imports = [];

      perSystem = { self', pkgs, config, ... }: {

        devShells.default = pkgs.mkShell {
          name = "haskell-template";
          meta.description = "Haskell development environment";
          inputsFrom = [
          ];
          nativeBuildInputs =
            [ inputs.ghc-wasm.packages.${pkgs.system}.all_9_12
              pkgs.hpack
              pkgs.just
              pkgs.haskellPackages.Cabal_3_14_2_0
              pkgs.haskell.compiler.ghc912
              (pkgs.haskell-language-server.override { supportedGhcVersions = [ "912" ]; })
              pkgs.haskellPackages.hoogle
            ];
        };
      };
    };
}
