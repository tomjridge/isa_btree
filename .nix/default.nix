{ }:

let
    pkgs = import <nixpkgs> {};
    stdenv = pkgs.stdenv;
    perl = pkgs.perl;    

    isabelle = import ./isabelle {
      inherit (pkgs) stdenv fetchurl perl nettools polyml;
      java = if stdenv.isLinux then pkgs.jre else pkgs.jdk;
    };

in 
stdenv.mkDerivation {

    name = "isaenv";

    buildInputs = [ perl isabelle ];

    configurePhase = "true"; 	# Skip configure

    buildPhase = "true"; # and build

    # eval "${!curPhase:-$curPhase}" from nix-shell, for testing

    installPhase = "true"; # don't want to install

    shellHook = "curPhase=buildPhase";

}
