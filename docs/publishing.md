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

1. Update `version` in `Cargo.toml`.
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

4. Inspect the archive under `target/package/`. It should contain only the
   manifest, lockfile, README, build script, and Rust sources.
5. Commit and push the version change.
6. Create a GitHub Release with the tag `vX.Y.Z`, exactly matching the
   `Cargo.toml` version.
7. Watch the `Package and publish` workflow. Its package job repeats the tests
   and archive verification before the publish job can run.
8. Verify the new release on crates.io and docs.rs.

If the release tag and manifest version differ, the workflow refuses to
publish.
