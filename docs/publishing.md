# Publishing rusty-alto

Releases are published to crates.io from GitHub Actions. Publishing is
permanent: an uploaded version cannot be replaced or deleted.

## One-time repository setup

1. Create a crates.io API token restricted to publishing `rusty-alto`.
2. In the GitHub repository, create an environment named `crates-io`.
3. Add the token to that environment as the secret
   `CARGO_REGISTRY_TOKEN`.
4. Optionally require reviewer approval for the `crates-io` environment.

The first release reserves the `rusty-alto` name. Confirm that the name is
available immediately before publishing.

## Release checklist

1. Add a concise entry to `CHANGELOG.md`, then update `version` in
   `Cargo.toml`.
2. Update `Cargo.lock`:

   ```sh
   cargo check
   ```

3. Run the local release checks:

   ```sh
   cargo test --locked --all-features
   cargo package --locked
   cargo package --list
   ```

4. Inspect the archive under `target/package/`. It should contain the manifest,
   lockfile, licenses, README, build script, Rust sources, and user-facing
   documentation. It must not contain benchmarks or benchmark results.
5. Commit and push the version change.
6. Tag that commit with `vX.Y.Z`, exactly matching the `Cargo.toml` version,
   and push the tag:

   ```sh
   git tag vX.Y.Z
   git push origin vX.Y.Z
   ```

7. Watch the `Package and publish` workflow. It repeats the tests and package
   verification before publishing the crate. A GitHub Release is not required.
8. Verify the new version on crates.io and docs.rs.

If the release tag and manifest version differ, the workflow refuses to
publish.
