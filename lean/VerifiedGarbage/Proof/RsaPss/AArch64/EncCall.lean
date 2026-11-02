module

public import VerifiedGarbage.Proof.RsaPss.EncodingContract
public import VerifiedGarbage.Proof.RsaPkcs1Sig.AArch64.Callee
import VerifiedGarbage.Proof.Framework.AArch64.RelCT
import VerifiedGarbage.Proof.Framework.Mem

/-!
# EMSA-PSS's encoding and its check on AArch64, as callees

RSASSA-PSS's signing and verification call `encode` and `checkEncoding`
(or their variants), of which they need only what their artifacts state:
that the code is `Verified` for the shared contract with some `stack`, and
that its frames fit in that stack (`Callee`). The call lemmas (`encCall`,
`chkCall`) evaluate those contracts into facts about the registers at the
call, and `encCallCT`, `chkCallCT` relate two calls with the same public
arguments.
-/

@[expose] public section

namespace VG.Proof.RsaPss.AArch64

open VG VG.AArch64
open VG.Proof.RsaPkcs1Sig.AArch64 (Callee ArgsEq argsEq_regs)

/-- `vg_rsa_pss_<H>_mgf1_<H>_encode` and its variants. -/
abbrev EncImpl (G : Spec.Mgf1.Hash) := Callee fun K => Proof.RsaPss.encodeContract G G abi K

/-- `vg_rsa_pss_<H>_mgf1_<H>_check_encoding` and its variants. -/
abbrev ChkImpl (G : Spec.Mgf1.Hash) := Callee fun K => Proof.RsaPss.checkEncodingContract G G abi K

/-- The `K` bytes below the stack pointer. -/
abbrev stkR (K : Nat) (t : State) : Region := ⟨t.sp - BitVec.ofNat 64 K, K⟩

/-! ## `encode` -/

/-- The regions a call of `encode` reads and writes. -/
abbrev encRd (D : Nat) (t : State) : List Region := [⟨t.gpr .x2, D⟩, ⟨t.gpr .x3, (t.gpr .x4).toNat⟩]
abbrev encWr (t : State) : List Region := [⟨t.gpr .x0, (t.gpr .x1).toNat⟩, ⟨t.gpr .x6, (t.gpr .x7).toNat * 8⟩]

/-- What a call of `encode` needs at the call: `em` at `x0` (`x1` bytes),
the digest (`D` bytes) at `x2`, the salt at `x3` (`x4` bytes), `emBits` in
`x5` and the working space at `x6` (`x7` words), apart where one is written,
from the `K` bytes below the stack pointer, and not wrapping around. -/
structure EncOk (D K : Nat) (t : State) : Prop where
  sp1 : K ≤ t.sp.toNat
  hrd : Covers (encRd D t) (t.rd ++ t.wr)
  hwr : Covers (encWr t) t.wr
  ed : (⟨t.gpr .x0, (t.gpr .x1).toNat⟩ : Region).Disjoint ⟨t.gpr .x2, D⟩
  esa : (⟨t.gpr .x0, (t.gpr .x1).toNat⟩ : Region).Disjoint ⟨t.gpr .x3, (t.gpr .x4).toNat⟩
  es : (⟨t.gpr .x0, (t.gpr .x1).toNat⟩ : Region).Disjoint ⟨t.gpr .x6, (t.gpr .x7).toNat * 8⟩
  ds : (⟨t.gpr .x2, D⟩ : Region).Disjoint ⟨t.gpr .x6, (t.gpr .x7).toNat * 8⟩
  sas : (⟨t.gpr .x3, (t.gpr .x4).toNat⟩ : Region).Disjoint ⟨t.gpr .x6, (t.gpr .x7).toNat * 8⟩
  ke : (stkR K t).Disjoint ⟨t.gpr .x0, (t.gpr .x1).toNat⟩
  kd : (stkR K t).Disjoint ⟨t.gpr .x2, D⟩
  ksa : (stkR K t).Disjoint ⟨t.gpr .x3, (t.gpr .x4).toNat⟩
  ks : (stkR K t).Disjoint ⟨t.gpr .x6, (t.gpr .x7).toNat * 8⟩
  we : (t.gpr .x0).toNat + (t.gpr .x1).toNat ≤ 2 ^ 64
  wd : (t.gpr .x2).toNat + D ≤ 2 ^ 64
  wsa : (t.gpr .x3).toNat + (t.gpr .x4).toNat ≤ 2 ^ 64
  ws : (t.gpr .x6).toNat + (t.gpr .x7).toNat * 8 ≤ 2 ^ 64
  b1 : 1 ≤ (t.gpr .x5).toNat
  b2 : (t.gpr .x5).toNat ≤ Proof.RsaPss.maxEmBits
  hel : (t.gpr .x1).toNat = Spec.RsaPss.emLength (t.gpr .x5).toNat
  hs : Proof.RsaPss.encodingScratchWords ≤ (t.gpr .x7).toNat

theorem EncOk.pre {G : Spec.Mgf1.Hash} {K : Nat} {t : State} (hK : 0 < K) (h : EncOk G.len K t) :
    (Proof.RsaPss.encodeContract G G abi K).pre (t.callEntry.withRegions (encRd G.len t) (encWr t)) := by
  obtain ⟨K, rfl⟩ : ∃ K', K = K' + 1 := ⟨K - 1, by omega⟩
  sig_pre [Proof.RsaPss.encodeContract, Proof.RsaPss.encodeSig, abi, argRegs, List.append_eq]
  exact ⟨h.sp1, h.ed, h.esa, h.es, h.ds, h.sas, h.ke, h.kd, h.ksa, h.ks, h.we, h.wd, h.wsa, h.ws, h.b1,
    h.b2, h.hel, h.hs⟩

/-- A call of `encode`. -/
theorem encCall {G : Spec.Mgf1.Hash} (c : EncImpl G) {t : State} {Q : State → Prop} (h : EncOk G.len c.stack t)
    (hQ : ∀ s', s'.rd = t.rd → s'.wr = t.wr → s'.sp = t.sp →
      Frame (encWr t ++ [below t.sp (16 * c.code.aarch64Depth)]) t.mem s'.mem →
      (∀ r ∈ preserved, r ≠ .x30 → s'.gpr r = t.gpr r) →
      (∀ r ∈ preservedV, (s'.v r).extractLsb' 0 64 = (t.v r).extractLsb' 0 64) →
      (match Spec.RsaPss.encode G G (Spec.Rsa.bytesAt t.mem (t.gpr .x2) G.len)
          (Spec.Rsa.bytesAt t.mem (t.gpr .x3) (t.gpr .x4).toNat) (t.gpr .x5).toNat with
        | some e => (s'.gpr .x0).setWidth 32 = (1 : BitVec 32) ∧
            Spec.Rsa.bytesAt s'.mem (t.gpr .x0) (t.gpr .x1).toNat = e
        | none => (s'.gpr .x0).setWidth 32 = (0 : BitVec 32)) → Q s') :
    WP isa (.call c.name c.code) t Q := by
  refine WP.callFV (k := Proof.RsaPss.encodeContract G G abi c.stack) c.verified.1 (h.pre c.pos)
    (Covers.append_left (Covers.trans h.hrd (Covers.refl _)) (Covers.right h.hwr)) h.hwr ?_
    (by have := c.le; have := c.depth; omega)
  intro s' hrd' hwr' hsp' hf hpres hvs hpost
  sig_post [Proof.RsaPss.encodeContract, Proof.RsaPss.encodeSig, abi, argRegs, List.append_eq] at hpost
  exact hQ s' hrd' hwr' hsp' hf hpres hvs hpost

/-- Two calls of `encode` leak alike if their arguments agree. -/
theorem encCallCT {G : Spec.Mgf1.Hash} (c : EncImpl G) {P : State → State → Prop}
    (hP : ∀ t₁ t₂, P t₁ t₂ → EncOk G.len c.stack t₁ ∧ EncOk G.len c.stack t₂ ∧ ArgsEq 0 t₁ t₂) :
    RelCT isa P (.call c.name c.code) fun _ _ => True := by
  refine RelCT.callEx c.verified.1 c.verified.2.1 fun t₁ t₂ hp => ?_
  obtain ⟨h₁, h₂, he⟩ := hP t₁ t₂ hp
  refine ⟨_, _, _, _, h₁.pre c.pos, h₂.pre c.pos, ?_,
    Covers.append_left (Covers.trans h₁.hrd (Covers.refl _)) (Covers.right h₁.hwr), h₁.hwr,
    Covers.append_left (Covers.trans h₂.hrd (Covers.refl _)) (Covers.right h₂.hwr), h₂.hwr⟩
  sig_pub [Proof.RsaPss.encodeContract, Proof.RsaPss.encodeSig, abi, argRegs, List.append_eq]
  obtain ⟨e0, e1, e2, e3, e4, e5, e6, e7⟩ := argsEq_regs he
  exact ⟨he.sp, e0, e1, e2, e3, e4, e5, e6, e7⟩

/-! ## `checkEncoding` -/

/-- The regions a call of `checkEncoding` reads and writes. -/
abbrev chkRd (D : Nat) (t : State) : List Region := [⟨t.gpr .x0, D⟩, ⟨t.gpr .x1, (t.gpr .x2).toNat⟩]
abbrev chkWr (t : State) : List Region := [⟨t.gpr .x6, (t.gpr .x7).toNat * 8⟩]

/-- What a call of `checkEncoding` needs at the call: the digest (`D`
bytes) at `x0`, `em` at `x1` (`x2` bytes), `emBits` in `x3` and the working
space at `x6` (`x7` words), apart from the working space and from the `K`
bytes below the stack pointer, and not wrapping around. -/
structure ChkOk (D K : Nat) (t : State) : Prop where
  sp1 : K ≤ t.sp.toNat
  hrd : Covers (chkRd D t) (t.rd ++ t.wr)
  hwr : Covers (chkWr t) t.wr
  ds : (⟨t.gpr .x0, D⟩ : Region).Disjoint ⟨t.gpr .x6, (t.gpr .x7).toNat * 8⟩
  es : (⟨t.gpr .x1, (t.gpr .x2).toNat⟩ : Region).Disjoint ⟨t.gpr .x6, (t.gpr .x7).toNat * 8⟩
  kd : (stkR K t).Disjoint ⟨t.gpr .x0, D⟩
  ke : (stkR K t).Disjoint ⟨t.gpr .x1, (t.gpr .x2).toNat⟩
  ks : (stkR K t).Disjoint ⟨t.gpr .x6, (t.gpr .x7).toNat * 8⟩
  wd : (t.gpr .x0).toNat + D ≤ 2 ^ 64
  we : (t.gpr .x1).toNat + (t.gpr .x2).toNat ≤ 2 ^ 64
  ws : (t.gpr .x6).toNat + (t.gpr .x7).toNat * 8 ≤ 2 ^ 64
  b1 : 1 ≤ (t.gpr .x3).toNat
  b2 : (t.gpr .x3).toNat ≤ Proof.RsaPss.maxEmBits
  hel : (t.gpr .x2).toNat = Spec.RsaPss.emLength (t.gpr .x3).toNat
  hs : Proof.RsaPss.encodingScratchWords ≤ (t.gpr .x7).toNat

theorem ChkOk.pre {G : Spec.Mgf1.Hash} {K : Nat} {t : State} (hK : 0 < K) (h : ChkOk G.len K t) :
    (Proof.RsaPss.checkEncodingContract G G abi K).pre (t.callEntry.withRegions (chkRd G.len t) (chkWr t)) := by
  obtain ⟨K, rfl⟩ : ∃ K', K = K' + 1 := ⟨K - 1, by omega⟩
  sig_pre [Proof.RsaPss.checkEncodingContract, Proof.RsaPss.checkEncodingSig, abi, argRegs, List.append_eq]
  exact ⟨h.sp1, h.ds, h.es, h.kd, h.ke, h.ks, h.wd, h.we, h.ws, h.b1, h.b2, h.hel, h.hs⟩

/-- A call of `checkEncoding`. -/
theorem chkCall {G : Spec.Mgf1.Hash} (c : ChkImpl G) {t : State} {Q : State → Prop} (h : ChkOk G.len c.stack t)
    (hQ : ∀ s', s'.rd = t.rd → s'.wr = t.wr → s'.sp = t.sp →
      Frame (chkWr t ++ [below t.sp (16 * c.code.aarch64Depth)]) t.mem s'.mem →
      (∀ r ∈ preserved, r ≠ .x30 → s'.gpr r = t.gpr r) →
      (∀ r ∈ preservedV, (s'.v r).extractLsb' 0 64 = (t.v r).extractLsb' 0 64) →
      (s'.gpr .x0).setWidth 32 = (if Spec.RsaPss.verifyEncoding G G (Spec.Rsa.bytesAt t.mem (t.gpr .x0) G.len)
        (Spec.Rsa.bytesAt t.mem (t.gpr .x1) (t.gpr .x2).toNat) (t.gpr .x3).toNat
        (Spec.RsaPss.expectedSaltLen (t.gpr .x4) ((t.gpr .x5).setWidth 32)) then (1 : BitVec 32) else 0) →
      Q s') :
    WP isa (.call c.name c.code) t Q := by
  refine WP.callFV (k := Proof.RsaPss.checkEncodingContract G G abi c.stack) c.verified.1 (h.pre c.pos)
    (Covers.append_left (Covers.trans h.hrd (Covers.refl _)) (Covers.right h.hwr)) h.hwr ?_
    (by have := c.le; have := c.depth; omega)
  intro s' hrd' hwr' hsp' hf hpres hvs hpost
  sig_post [Proof.RsaPss.checkEncodingContract, Proof.RsaPss.checkEncodingSig, abi, argRegs, List.append_eq] at hpost
  exact hQ s' hrd' hwr' hsp' hf hpres hvs hpost

/-- Two calls of `checkEncoding` leak alike if their arguments agree. -/
theorem chkCallCT {G : Spec.Mgf1.Hash} (c : ChkImpl G) {P : State → State → Prop}
    (hP : ∀ t₁ t₂, P t₁ t₂ → ChkOk G.len c.stack t₁ ∧ ChkOk G.len c.stack t₂ ∧ ArgsEq 0 t₁ t₂) :
    RelCT isa P (.call c.name c.code) fun _ _ => True := by
  refine RelCT.callEx c.verified.1 c.verified.2.1 fun t₁ t₂ hp => ?_
  obtain ⟨h₁, h₂, he⟩ := hP t₁ t₂ hp
  refine ⟨_, _, _, _, h₁.pre c.pos, h₂.pre c.pos, ?_,
    Covers.append_left (Covers.trans h₁.hrd (Covers.refl _)) (Covers.right h₁.hwr), h₁.hwr,
    Covers.append_left (Covers.trans h₂.hrd (Covers.refl _)) (Covers.right h₂.hwr), h₂.hwr⟩
  sig_pub [Proof.RsaPss.checkEncodingContract, Proof.RsaPss.checkEncodingSig, abi, argRegs, List.append_eq]
  obtain ⟨e0, e1, e2, e3, e4, e5, e6, e7⟩ := argsEq_regs he
  exact ⟨he.sp, e0, e1, e2, e3, e4, by rw [e5], e6, e7⟩

end VG.Proof.RsaPss.AArch64
