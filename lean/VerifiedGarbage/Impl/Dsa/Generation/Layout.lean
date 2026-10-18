module

public import VerifiedGarbage.Impl.Dsa.Layout

/-! # Shared storage plan for verified DSA parameter generation

Hashing, candidate arithmetic, primality testing and generator exponentiation
reuse their existing verified workspaces. Saved candidates, the exponent,
and loop state remain outside those workspaces. All offsets are bytes from
the generation scratch base; only the final domain-check area varies in size.
-/

@[expose] public section
namespace VG.Impl.Dsa.Generation.Layout

def parent : Nat := 0
def hash : Nat := 16384
def wrappedSeed : Nat := 24576
def hashes : Nat := 24640
def shaped : Nat := 25024
def q : Nat := 25408
def p : Nat := 25472
def exponent : Nat := 25856
def g : Nat := 26240
def witness : Nat := 26624
def packed : Nat := 27008
def control : Nat := 27840
def arithmetic : Nat := 28672
def arithmeticBytes : Nat := 12288
def domainCheck : Nat := 40960

def usedBytes (pLen : Nat) : Nat := domainCheck + 128 * pLen

/-- Disjoint persistent buffers and temporary workspaces. -/
def areas (pLen : Nat) : List (Nat × Nat) :=
  [(parent, Dsa.Layout.activeBytes), (hash, 8192), (wrappedSeed, 32),
   (hashes, 384), (shaped, 384), (q, 32), (p, 384), (exponent, 384),
   (g, 384), (witness, 384), (packed, 800), (control, 512),
   (arithmetic, arithmeticBytes), (domainCheck, 128 * pLen)]

end VG.Impl.Dsa.Generation.Layout
