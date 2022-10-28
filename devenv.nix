{ pkgs, ... }:
{
  # https://devenv.sh/basics/
  env.GREET = "devenv";

  # https://devenv.sh/packages/
  packages = [ pkgs.git ];

  enterShell = ''
    hello
    git --version
  '';

  # https://devenv.sh/languages/
  languages.nix.enable = true;

  # https://devenv.sh/scripts/
  scripts.hello.exec = "echo hello from $GREET";

  # https://devenv.sh/pre-commit-hooks/
  pre-commit = {
    # settings.rust.toolchain = "stable";
    hooks = {
      clippy.enable = true;
      rustfmt.enable = true;
    };
  };

  # https://devenv.sh/processes/
  # processes.ping.exec = "ping example.com";
}
