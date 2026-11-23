# Releasing

Releases are built and published by [.github/workflows/release.yml](../.github/workflows/release.yml) when a `v*` tag is pushed.

## Versioning

Puddi follows [Semantic Versioning](https://semver.org/). During 0.x, a minor release may contain breaking changes and a patch release contains only fixes. A tag with a hyphen (`v0.2.0-rc.1`) is published as a prerelease.

## Steps

1. Make sure CI is green on `main`.
2. Set `version` in `Cargo.toml` to the new version, and run `cargo build` so `Cargo.lock` follows.
3. In `CHANGELOG.md`, rename `## [Unreleased]` to `## [X.Y.Z] - YYYY-MM-DD` and start a new empty `## [Unreleased]` above it. The release notes are taken from this section, so write them for users: language changes, toolchain changes, breaking changes with migration notes, and the known non-conformance from the conformance suite.
4. Update the version in the `cargo install ... --tag` line of `README.md`.
5. Open a release PR against `main`. A maintainer can enable auto-merge while the required CI checks run.
6. Once the PR is merged and CI is green on `main`, tag the commit that merged the release PR. Replace `MERGED_COMMIT_SHA` with that commit's SHA and push the tag.

   ```sh
   git fetch origin main
   git tag -a vX.Y.Z MERGED_COMMIT_SHA -m "Puddi X.Y.Z"
   git push origin vX.Y.Z
   ```

The workflow then:

- checks that the tag matches the `Cargo.toml` version;
- builds `pud` for x86_64 and arm64 Linux, x86_64 and arm64 macOS, and x86_64 Windows;
- runs the conformance suite with `--strict-coverage` on every binary it can execute (all but the cross-compiled x86_64 macOS build);
- packages each binary with the README and licenses, with a `.sha256` file;
- creates the GitHub release with the changelog section as notes, all archives, `SHA256SUMS`, `install.sh` and `install.ps1`.

The install scripts download `releases/latest`, so a new release is picked up by `curl ... | sh` as soon as it is published (prereleases are not "latest").

## After the release

- In [puddi-docs](https://github.com/puddi-lang/puddi-docs), set `PUDDI_VERSION` to the new tag, update the Simplified Chinese specification and changelog with their release markers, and revise affected chapters in both editions. CI checks the examples against the new release.
- If something went wrong, delete the GitHub release and the tag, fix the problem on `main`, and tag again. Do not move a tag that has been public for a while; release a patch version instead.
