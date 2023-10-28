{
  inputs = {
    flake-utils.url = "github:numtide/flake-utils";
  };
  outputs = { self, nixpkgs, flake-utils }:
    flake-utils.lib.eachDefaultSystem (system:
      let 
        pkgs = import nixpkgs { inherit system; };
        ghcVersion = "946";
      in {
        devShell = pkgs.mkShell {
          buildInputs = with pkgs; [
            haskell.packages."ghc${ghcVersion}".ghc
            cabal-install
            (haskell-language-server.override { supportedGhcVersions = [ ghcVersion ]; })
            haskellPackages.fourmolu

            gdb
            
            llvmPackages_15.llvm
            libxml2.dev
          ];
          
          LD_LIBRARY_PATH = "${pkgs.xml2}/lib";

          # TODO: make this better. It's a `metis` implementation detail.
          LIBC_LIB_PATH = pkgs.stdenv.cc.libc;
        };
      }
    );
}
