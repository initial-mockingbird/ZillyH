{
  inputs = {
    nixpkgs.url = "github:nixos/nixpkgs/nixpkgs-unstable";
    # nixpkgs.url = "github:nixos/nixpkgs/b75693fb46bfaf09e662d09ec076c5a162efa9f6";
    flake-parts.url = "github:hercules-ci/flake-parts";
    # haskell-flake.url = "github:srid/haskell-flake";
    ghc-wasm.url = "gitlab:haskell-wasm/ghc-wasm-meta?host=gitlab.haskell.org";
    singletons-base.url = "github:initial-mockingbird/singletons/d6c49e43e25c73540446a220148acf796be42409";
    singletons-base.flake = false;
    #
    # https://github.com/initial-mockingbird/singletons/tree/5eb19a576ffb109d45218b7a7d43acdd82947082/singletons
    singletons.url = "github:initial-mockingbird/singletons/5eb19a576ffb109d45218b7a7d43acdd82947082";
    singletons.flake = false;
    #https://github.com/initial-mockingbird/singletons/tree/5eb19a576ffb109d45218b7a7d43acdd82947082/singletons-th
    singletons-th.url = "github:initial-mockingbird/singletons/5eb19a576ffb109d45218b7a7d43acdd82947082";
    singletons-th.flake = false;
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
            [ inputs.ghc-wasm.packages.${pkgs.system}.all_9_10
              # pkgs.x86_64-linux.default
              # pkgs.defaultPackage.x86_64-linux
              # pkgs.86_64-linux
              pkgs.hpack
              pkgs.just
              pkgs.glibc
              pkgs.gnused
              pkgs.nodejs
              # pkgs.nodePackages.npm
              pkgs.pnpm
              pkgs.esbuild
              pkgs.nodePackages.typescript
              pkgs.nodePackages.typescript-language-server
              pkgs.bun
              pkgs.haskellPackages.Cabal_3_14_0_0
              pkgs.haskell.compiler.ghc910
              (pkgs.haskell-language-server.override { supportedGhcVersions = [ "910" ]; })
              pkgs.haskellPackages.hoogle
            ];
        };
      };
    };
}
