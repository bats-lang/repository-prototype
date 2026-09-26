# Publishing setup

Package repositories publish to this repository from CI when a change
merges to their `main`. The publish job builds the archive, pushes it to a
`publish/<package>-<version>` branch here, and opens a pull request that
merges itself once the `verify` check passes.

This needs three one-time settings, all done by an owner of the
`bats-lang` organization.

## 1. A fine-grained token that can open pull requests here

The default `GITHUB_TOKEN` of a package repository cannot write to another
repository, and pull requests it opens do not start workflows (so `verify`
would never run). A fine-grained personal access token scoped to this one
repository does both.

1. On GitHub, click your profile picture (top right), then **Settings**.
2. In the left sidebar, click **Developer settings**.
3. Under **Personal access tokens**, click **Fine-grained tokens**.
4. Click **Generate new token**.
5. **Token name**: `bats-lang publish`.
6. **Expiration**: pick a date (a year is fine) and put a reminder in your
   calendar to rotate it: when it expires, publishing stops.
7. **Description**: `Opens publish PRs in bats-lang/repository-prototype`.
8. **Resource owner**: `bats-lang`. (If the organization requires approval
   for tokens, fill in the justification box that appears; see below.)
9. **Repository access**: **Only select repositories**, then choose
   `bats-lang/repository-prototype`. Nothing else.
10. **Permissions → Repository permissions**:
    - **Contents**: Read and write
    - **Pull requests**: Read and write
    - (**Metadata**: Read-only is added automatically.)

    Leave everything else at **No access**.
11. Click **Generate token** and copy it. It is shown only once.

If the organization requires administrator approval for fine-grained
tokens, the token is "pending" until approved: as an owner, open the
organization's **Settings**, and in the left sidebar under **Personal access
tokens** click **Pending requests**, then the token's name, then
**Approve**.

## 2. The token as an organization secret

1. Go to the organization page (`github.com/bats-lang`) and click
   **Settings**.
2. In the left sidebar, under **Security**, click **Secrets and variables**,
   then **Actions**.
3. On the **Secrets** tab, click **New organization secret**.
4. **Name**: `REPO_PUBLISH_TOKEN`.
5. **Value**: paste the token.
6. **Repository access**: **Selected repositories**, and pick every package
   repository that publishes (argparse, arith, array, builder, decompress,
   dict, dom, env, file, file-input, html, json, list, path, process,
   promise, result, sha256, sort, str, toml, xml-tree, zip, bridge, css,
   widget, pwa, …). Add a repository here when a new package is created.
7. Click **Add secret**.

## 3. Auto-merge, and `main` protected by `verify`

Auto-merge lets a pull request be marked "merge when the required checks
pass"; the publish job marks its pull requests that way, so nobody has to
press the button. It only means something together with a required check,
which is what branch protection adds. Both are available for public
repositories on the free plan.

In this repository (`bats-lang/repository-prototype`):

1. **Settings → General**, section **Pull Requests**: tick
   **Allow auto-merge**.
2. **Settings → Branches → Add branch protection rule** (the classic rule):
   - **Branch name pattern**: `main`
   - Tick **Require status checks to pass before merging**, then search for
     and add the `verify` check. (It appears in the search only after the
     `verify` workflow has run once, on any pull request.)
   - Click **Create**.

Pull requests into `main` then merge only when `verify` is green: for
publish pull requests that happens by itself, for everything else as
before.
