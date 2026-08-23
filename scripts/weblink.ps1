<#
.SYNOPSIS
  Turn a file in this repository into a no-install Lean web-editor link.

.DESCRIPTION
  PowerShell equivalent of scripts/weblink.sh, for working from PowerShell or
  the VS Code terminal on Windows without going through Git Bash.

  Prints a URL that opens the file in the Lean 4 web editor
  (https://live.lean-lang.org), which runs Lean and Mathlib in a browser tab
  with no account and nothing to install. The link points at the raw file on
  GitHub, so editing and pushing updates every link already sent.

  NOTE: the web editor serves the LATEST Mathlib, not the v4.33.0 this seminar
  pins. A file that passes CI can still fail there after an upstream rename.
  Click the link yourself before sending it -- that click is the only check.

.EXAMPLE
  .\scripts\weblink.ps1 Seminar\Session01_Demo\Demo.lean

.EXAMPLE
  .\scripts\weblink.ps1 Seminar\Session01_Demo\Demo.lean -Copy
#>
[CmdletBinding()]
param(
  [Parameter(Mandatory = $true, Position = 0)]
  [string] $Path,

  # Branch to link to. Defaults to the current branch.
  [string] $Branch,

  # Skip the HTTP check (offline use).
  [switch] $NoCheck,

  # Also copy the link to the clipboard.
  [switch] $Copy
)

$ErrorActionPreference = 'Stop'

function Fail($msg) {
  Write-Host "error: $msg" -ForegroundColor Red
  exit 1
}

# --- move to the repository root ------------------------------------------
$root = git rev-parse --show-toplevel 2>$null
if ($LASTEXITCODE -ne 0 -or -not $root) { Fail "not inside a git repository" }
Set-Location $root

# --- which repository, which branch ---------------------------------------
$repo = $env:SEMINAR_REPO
if (-not $repo) {
  $origin = git remote get-url origin 2>$null
  if ($LASTEXITCODE -ne 0 -or -not $origin) {
    Fail "no git remote 'origin'; set `$env:SEMINAR_REPO = 'owner/name'"
  }
  $repo = $origin -replace '^(https://github\.com/|git@github\.com:)', '' -replace '\.git$', ''
}

if (-not $Branch) {
  $Branch = git rev-parse --abbrev-ref HEAD
}

# --- normalise the path: backslashes in, forward slashes out --------------
$rel = $Path -replace '\\', '/'
$rel = $rel -replace '^\./', ''

if (-not (Test-Path -LiteralPath $rel -PathType Leaf)) {
  Fail "no such file: $rel"
}

# --- is this the file they will actually see? -----------------------------
git diff --quiet -- $rel 2>$null
$dirty = ($LASTEXITCODE -ne 0)
git diff --quiet --cached -- $rel 2>$null
if ($LASTEXITCODE -ne 0) { $dirty = $true }
if ($dirty) {
  Write-Warning "$rel has uncommitted changes -- the link serves the committed version."
}

git rev-parse --verify --quiet "origin/$Branch" > $null 2>&1
if ($LASTEXITCODE -eq 0) {
  git diff --quiet "origin/$Branch" -- $rel 2>$null
  if ($LASTEXITCODE -ne 0) {
    Write-Warning "$rel differs from origin/$Branch -- push before sending the link."
  }
} else {
  Write-Warning "no origin/$Branch locally; cannot tell whether $rel is pushed."
}

# --- build the link --------------------------------------------------------
$raw  = "https://raw.githubusercontent.com/$repo/$Branch/$rel"
$base = $env:LEAN_WEB
if (-not $base) { $base = 'https://live.lean-lang.org' }
$link = "$base/#url=" + [System.Uri]::EscapeDataString($raw)

# --- does it actually resolve? --------------------------------------------
if (-not $NoCheck) {
  try {
    $resp = Invoke-WebRequest -Uri $raw -Method Head -UseBasicParsing -TimeoutSec 20
    $code = [int] $resp.StatusCode
  } catch {
    $code = 0
    if ($_.Exception.Response) { $code = [int] $_.Exception.Response.StatusCode }
  }
  if ($code -ne 200) {
    Write-Host "error: $raw returned HTTP $code." -ForegroundColor Red
    Write-Host "       Usually this means the branch or the file has not been pushed."
    exit 1
  }
}

if ($Copy) {
  try { Set-Clipboard -Value $link; Write-Host "(copied to clipboard)" -ForegroundColor DarkGray }
  catch { Write-Warning "could not copy to clipboard" }
}

Write-Output $link
