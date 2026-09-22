#!/usr/bin/env bash

set -euo pipefail

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
upstream_repository="https://github.com/TheJustinSunPrize/awards.git"
upstream_ref="${JSP_UPSTREAM_REF:-main}"
vendor_parent="${repo_root}/docs/vendor"
destination="${vendor_parent}/jsp"
temporary_directory="$(mktemp -d)"
checkout_directory="${temporary_directory}/awards"
prepared_snapshot="${temporary_directory}/snapshot"
stage_directory=""
backup_directory="${temporary_directory}/previous-snapshot"
replacement_started=false
had_destination=false

required_paths=(
  README.md
  CONTRIBUTING.md
  LICENSE
  LICENSE-CONTENT
  docs/award-process.md
  docs/attribution.md
  docs/grading.md
  docs/records.md
  docs/verification.md
  problems/README.md
  skills/lean-verify/SKILL.md
  .github/ISSUE_TEMPLATE/claim-award.yml
)

fail() {
  printf 'JSP documentation sync failed: %s\n' "$*" >&2
  exit 1
}

cleanup() {
  local status="$?"

  trap - EXIT
  if [[ "${replacement_started}" == true ]]; then
    rm -rf "${destination}"
    if [[ "${had_destination}" == true && -e "${backup_directory}" ]]; then
      mv "${backup_directory}" "${destination}"
    fi
  fi
  rm -rf "${stage_directory}" "${backup_directory}" "${temporary_directory}"
  exit "${status}"
}

trap cleanup EXIT

if ! git check-ref-format --allow-onelevel "${upstream_ref}"; then
  fail "invalid upstream ref '${upstream_ref}'"
fi

git init --quiet "${checkout_directory}"
git -C "${checkout_directory}" remote add origin "${upstream_repository}"
git -C "${checkout_directory}" sparse-checkout init --no-cone
git -C "${checkout_directory}" sparse-checkout set --no-cone -- \
  /README.md \
  /CONTRIBUTING.md \
  /LICENSE \
  /LICENSE-CONTENT \
  /docs/award-process.md \
  /docs/attribution.md \
  /docs/grading.md \
  /docs/records.md \
  /docs/verification.md \
  /problems/README.md \
  '/problems/catalog-*.md' \
  /skills/lean-verify/SKILL.md \
  /.github/ISSUE_TEMPLATE/claim-award.yml

if ! git -C "${checkout_directory}" fetch --quiet --depth 1 --filter=blob:none \
  origin "${upstream_ref}"; then
  fail "could not resolve upstream ref '${upstream_ref}'"
fi
git -C "${checkout_directory}" checkout --quiet --detach FETCH_HEAD

upstream_commit="$(git -C "${checkout_directory}" rev-parse --verify HEAD)"
if [[ ! "${upstream_commit}" =~ ^[0-9a-f]{40}$ ]]; then
  fail "resolved upstream commit is not a full SHA"
fi

validate_source_file() {
  local relative_path="$1"
  local source_path="${checkout_directory}/${relative_path}"
  local resolved_path

  if [[ -L "${source_path}" || ! -f "${source_path}" ]]; then
    fail "required upstream path '${relative_path}' is not a regular file"
  fi

  resolved_path="$(realpath --canonicalize-existing "${source_path}")"
  if [[ "${resolved_path}" != "${checkout_directory}/"* ]]; then
    fail "upstream path '${relative_path}' escapes checkout"
  fi
}

for required_path in "${required_paths[@]}"; do
  validate_source_file "${required_path}"
done

mapfile -t catalog_paths < <(
  find "${checkout_directory}/problems" -maxdepth 1 -type f -name 'catalog-*.md' \
    -printf '%f\n' | sort
)
if [[ "${#catalog_paths[@]}" -eq 0 ]]; then
  fail "no upstream problem catalog files were found"
fi
for catalog_path in "${catalog_paths[@]}"; do
  validate_source_file "problems/${catalog_path}"
done

mkdir -p "${prepared_snapshot}/docs" \
  "${prepared_snapshot}/problems" \
  "${prepared_snapshot}/skills/lean-verify" \
  "${prepared_snapshot}/.github/ISSUE_TEMPLATE"

cp "${checkout_directory}/README.md" "${prepared_snapshot}/UPSTREAM_README.md"
for required_path in "${required_paths[@]}"; do
  if [[ "${required_path}" != README.md ]]; then
    cp "${checkout_directory}/${required_path}" \
      "${prepared_snapshot}/${required_path}"
  fi
done
for catalog_path in "${catalog_paths[@]}"; do
  cp "${checkout_directory}/problems/${catalog_path}" \
    "${prepared_snapshot}/problems/${catalog_path}"
done

printf '%s\n' "${upstream_ref}" > "${prepared_snapshot}/UPSTREAM_REF"
printf '%s\n' "${upstream_commit}" > "${prepared_snapshot}/UPSTREAM_COMMIT"
cat > "${prepared_snapshot}/README.md" <<'EOF'
# Managed Justin Sun Prize reference snapshot

This is a managed, read-only snapshot of the official
[TheJustinSunPrize/awards](https://github.com/TheJustinSunPrize/awards)
repository. The source ref is recorded in `UPSTREAM_REF`; the full resolved
commit is recorded in `UPSTREAM_COMMIT`.

## Source

https://github.com/TheJustinSunPrize/awards

## Managed by

`scripts/sync_jsp_docs.sh`

Do not edit this directory manually. Refresh it only with:

```bash
./scripts/sync_jsp_docs.sh
```

The upstream repository remains authoritative. This snapshot supports
reproducible planning, review, and scanning; it is not a fork and it does not
include live GitHub pull-request or Issue state. Check that state separately.
EOF

for required_path in "${required_paths[@]:1}"; do
  if [[ ! -f "${prepared_snapshot}/${required_path}" ]]; then
    fail "staged snapshot is missing '${required_path}'"
  fi
done
if [[ ! -f "${prepared_snapshot}/UPSTREAM_README.md" || \
      ! -f "${prepared_snapshot}/problems/README.md" || \
      ! -f "${prepared_snapshot}/skills/lean-verify/SKILL.md" || \
      ! -f "${prepared_snapshot}/.github/ISSUE_TEMPLATE/claim-award.yml" ]]; then
  fail "staged snapshot is incomplete"
fi
if [[ ! "$(<"${prepared_snapshot}/UPSTREAM_COMMIT")" =~ ^[0-9a-f]{40}$ ]]; then
  fail "staged commit metadata is invalid"
fi

mkdir -p "${vendor_parent}"
stage_directory="$(mktemp -d "${vendor_parent}/.jsp-sync-stage.XXXXXX")"
cp -a "${prepared_snapshot}/." "${stage_directory}/"

if [[ -e "${destination}" || -L "${destination}" ]]; then
  had_destination=true
  mv "${destination}" "${backup_directory}"
fi
replacement_started=true
mv "${stage_directory}" "${destination}"
stage_directory=""
replacement_started=false
rm -rf "${backup_directory}"

printf 'source: %s\n' "${upstream_repository}"
printf 'ref: %s\n' "${upstream_ref}"
printf 'resolved commit: %s\n' "${upstream_commit}"
printf 'catalog files: %s\n' "${#catalog_paths[@]}"
printf 'destination: %s\n' "${destination}"
