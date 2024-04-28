{ nixpkgsFile ? ./nix/pkgs.nix
}:
with (import nixpkgsFile);
pkgs.mkShell {
  nativeBuildInputs = [
    pkgs.haskell.compiler.ghc90
    pkgsUnstable.cabal-install
    pkgs.git
    pkgs.zlib
  ];

  shellHook = ''
    export PATH=$(pwd)/hls:$PATH # Run the command '$(nix-build build-hls.sh.nix)/bin/build-hls.sh' to install HLS in this directory
  '';
}
