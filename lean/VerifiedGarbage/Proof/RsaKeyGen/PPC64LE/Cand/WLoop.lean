module

public import VerifiedGarbage.Proof.RsaKeyGen.PPC64LE.Cand.WDraw
public import VerifiedGarbage.Proof.RsaKeyGen.MrIter
public import VerifiedGarbage.Proof.RsaKeyGen.Generate
import VerifiedGarbage.Proof.RsaKeyGen.MrLoopAt
import VerifiedGarbage.Proof.RsaKeyGen.PPC64LE.Cand.Slot
import VerifiedGarbage.Proof.RsaKeyGen.PPC64LE.Cand.Out
import VerifiedGarbage.Proof.RsaKeyGen.PPC64LE.Cand.WLoad
import VerifiedGarbage.Proof.MillerRabin.PPC64LE.Search.GeFlag
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.PPC64LE.Step
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega

/-!
# A candidate on PPC64LE: the witnesses' loop

`millerRabin_ok`: `Witness.millerRabin` leaves `hStat` and `hUsed` as
`primalityTest c` of the tape after the candidate's octets says: 0 if it ran
out of octets, else 1 (probably prime) or 2 (composite), and the octets used.
Its invariant, after `k` witnesses passed, is `MrAt` (`MrIter.lean`) and the
header's counts (`St`).
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.PPC64LE.Cand

open VG VG.PPC64LE VG.Proof.Mont VG.Proof.Bignum.PPC64LE
open VG.Impl.RsaKeyGen.PPC64LE.Witness (draw hUni)
open VG.Impl.MillerRabin.PPC64LE.Search (ldh sth geFlag hRand hRandLen hUsed hK hIdx hChecks hStat)
open VG.Proof.MillerRabin.PPC64LE.Search (Prep geFlag_ok)
open VG.Proof.MillerRabin.PPC64LE (RoundImpl arr)
open VG.Proof.Bignum (slot)
open VG.Proof.RsaKeyGen (MrAt mrS goS wit)

/-- The registers the loop writes. -/
def lpRegs : List Reg :=
  [.r0, .r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10, .r12, .r14, .r15, .r16, .r17, .r20, .r21]

theorem not_mem_of_sub {xs ys : List Reg} (h : ∀ r ∈ xs, r ∈ ys) {r : Reg} (hr : r ∉ ys) : r ∉ xs :=
  fun e => hr (h r e)

/-- The header words the loop changes, as numbers of words. -/
def lpWords : List Nat := [23, 26, 29, 30, 1, 20, 22, 19, 2]

/-- What the loop keeps of its start `s`: the header words but the ones it
counts in, the memory but the working space and the stack below, the
regions, and the registers it does not write. -/
structure LKeep (s : State) (B : Addr) (L : Nat) (t : State) : Prop where
  hdr : ∀ d, d + 8 ≤ 256 → (∀ k ∈ lpWords, d + 8 ≤ 8 * k ∨ 8 * k + 8 ≤ d) → word t.mem B d = word s.mem B d
  frame : Frame [⟨B, 8 * L⟩, below s.sp 176] s.mem t.mem
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp
  cs : ∀ r ∈ preserved, r ∉ Pub.montRegs → r ∉ lpRegs → t.gpr r = s.gpr r

theorem LKeep.keep {s t t' : State} {B : Addr} {L : Nat} {rs : List Reg} (h : LKeep s B L t) (K : Keep rs t t')
    (hm : t'.mem = t.mem) (hr : ∀ x ∈ rs, x ∈ lpRegs) : LKeep s B L t' :=
  ⟨fun d hd hk => by rw [hm]; exact h.hdr d hd hk, by rw [hm]; exact h.frame, K.rd.trans h.rd, K.wr.trans h.wr,
    K.sp.trans h.sp, fun x hx h1 h2 => (K.gpr x (not_mem_of_sub hr h2)).trans (h.cs x hx h1 h2)⟩

/-- The loop after `k` witnesses passed. -/
structure St (s : State) (B : Addr) (L w c : Nat) (r : Spec.RsaKeyGen.Rand) (k : Nat) (t : State) : Prop
    extends LKeep s B L t where
  prep : Prep t B L w c
  used : word t.mem B (8 * hUsed) = BitVec.ofNat 64 (8 * w * (k + 1))
  idx : word t.mem B (8 * hIdx) = BitVec.ofNat 64 (mrS c (8 * w) r k).1
  uni : word t.mem B (8 * hUni) = BitVec.ofNat 64 (mrS c (8 * w) r k).2
  stat : word t.mem B (8 * hStat) = BitVec.ofNat 64 4

/-- What the loop leaves. -/
structure MrOut (s : State) (B : Addr) (L w c rl : Nat) (r : Spec.RsaKeyGen.Rand) (t : State) : Prop
    extends LKeep s B L t where
  prep : Prep t B L w c
  res : match Spec.RsaKeyGen.primalityTest c (r.drop (8 * w)) with
    | none => word t.mem B (8 * hStat) = BitVec.ofNat 64 0
    | some (b, rest) => word t.mem B (8 * hStat) = BitVec.ofNat 64 (if b then 1 else 2) ∧
        word t.mem B (8 * hUsed) = BitVec.ofNat 64 (rl - rest.length)

/-- The loop's facts about its start. -/
structure LIn (s : State) (B Ra : Addr) (L w c rl ch : Nat) (r : Spec.RsaKeyGen.Rand) : Prop where
  h35 : slot w VG.Impl.RsaKeyGen.PPC64LE.Candidate.nArr ≤ 8 * L
  shape : PrimeShape (64 * w) c
  hch : ch = Spec.RsaKeyGen.checksForSize (64 * w)
  hch' : ch < 2 ^ 63
  rand : word s.mem B (8 * hRand) = Ra
  rlen : word s.mem B (8 * hRandLen) = BitVec.ofNat 64 rl
  kk : word s.mem B (8 * hK) = BitVec.ofNat 64 (8 * w)
  chk : word s.mem B (8 * hChecks) = BitVec.ofNat 64 ch
  hrl : rl < 2 ^ 64
  tape : Spec.Rsa.bytesAt s.mem Ra rl = r
  rN : ∀ i < rl, InRegions (s.rd ++ s.wr) (off Ra i) 1
  rD : ∀ ρ ∈ [(⟨B, 8 * L⟩ : Region), below s.sp 176], (⟨Ra, rl⟩ : Region).Disjoint ρ
  wr : (⟨B, 8 * L⟩ : Region) ∈ s.wr
  hsp : 176 ≤ s.sp.toNat
  hstk : (below s.sp 176).Disjoint ⟨B, 8 * L⟩

theorem mrS_fst (c L : Nat) (r : Spec.RsaKeyGen.Rand) (k : Nat) : (mrS c L r k).1 = k + 1 := by
  rw [← VG.Proof.RsaKeyGen.mrSB_eq_mrS]; exact VG.Proof.RsaKeyGen.mrSB_first _ _ _ _ _

theorem mrS_snd (c L : Nat) (r : Spec.RsaKeyGen.Rand) (k : Nat) : (mrS c L r k).2 ≤ k := by
  rw [← VG.Proof.RsaKeyGen.mrSB_eq_mrS]; exact VG.Proof.RsaKeyGen.mrSB_uniform_le _ _ _ _ _

theorem round_eq (c x : Nat) :
    Proof.MillerRabin.Round.round c x =
      Spec.RsaKeyGen.mrIteration c (Spec.Rsa.splitTwos (c - 1)).1 (Spec.Rsa.splitTwos (c - 1)).2 x := rfl

theorem statOf_eq {c L ch : Nat} {r : Spec.RsaKeyGen.Rand} {k : Nat} (b : Bool) :
    statOf (mrS c L r k).1 ((mrS c L r k).2 + if b then 1 else 0) ch =
      if (mrS c L r k).1 + 1 ≤ Spec.RsaKeyGen.blindedChecks ∨ (mrS c L r k).2 + (if b then 1 else 0) < ch
      then 4 else 1 := by
  generalize (mrS c L r k).1 = I
  generalize (mrS c L r k).2 + (if b then 1 else 0) = U
  unfold statOf Spec.RsaKeyGen.blindedChecks
  split <;> split <;> omega

theorem St.keep {s t t' : State} {B : Addr} {L w c : Nat} {r : Spec.RsaKeyGen.Rand} {k : Nat} {rs : List Reg}
    (h : St s B L w c r k t) (K : Keep rs t t') (hm : t'.mem = t.mem)
    (hr : ∀ x ∈ rs, x ∈ lpRegs := by decide)
    (he : ∀ x ∈ VG.Proof.MillerRabin.PPC64LE.envRegs, x ∉ rs := by decide) : St s B L w c r k t' :=
  ⟨h.toLKeep.keep K hm hr, h.prep.keep (h.prep.env.keep K he) (fun _ _ => by rw [hm]) (fun _ _ => by rw [hm]),
    by rw [hm]; exact h.used, by rw [hm]; exact h.idx, by rw [hm]; exact h.uni, by rw [hm]; exact h.stat⟩

theorem MrOut.keep {s t t' : State} {B : Addr} {L w c rl : Nat} {r : Spec.RsaKeyGen.Rand} {rs : List Reg}
    (h : MrOut s B L w c rl r t) (K : Keep rs t t') (hm : t'.mem = t.mem)
    (hr : ∀ x ∈ rs, x ∈ lpRegs := by decide)
    (he : ∀ x ∈ VG.Proof.MillerRabin.PPC64LE.envRegs, x ∉ rs := by decide) : MrOut s B L w c rl r t' :=
  ⟨h.toLKeep.keep K hm hr, h.prep.keep (h.prep.env.keep K he) (fun _ _ => by rw [hm]) (fun _ _ => by rw [hm]),
    by rw [hm]; exact h.res⟩

/-- A draw keeps what the loop keeps. -/
theorem LKeep.draw {s t t' : State} {B Ra : Addr} {L w c u I U ch : Nat} (h : LKeep s B L t)
    (hd : DrPost t B Ra L w c u I U ch t') : LKeep s B L t' :=
  ⟨fun d hd' hk => (hd.hdr d hd' hk).trans (h.hdr d hd' hk), h.frame.trans (by have := hd.frame; rwa [h.sp] at this),
    hd.rd.trans h.rd, hd.wr.trans h.wr, hd.sp.trans h.sp, fun x hx h1 h2 =>
      (hd.cs x hx h1 (not_mem_of_sub (by decide) h2) (not_mem_of_sub (by decide) h2)
        (not_mem_of_sub (by decide) h2)).trans (h.cs x hx h1 h2)⟩

/-- A write of a header word the loop counts in. -/
theorem LKeep.write {s t t' : State} {B : Addr} {L : Nat} {rs : List Reg} (h : LKeep s B L t) {d : Nat}
    (hd : d ∈ lpWords) (hL : 256 ≤ 8 * L) {v : BitVec 64} (K : Keep rs t t')
    (hm : t'.mem = t.mem.writeW (off B (8 * d)) v) (hr : ∀ x ∈ rs, x ∈ lpRegs) : LKeep s B L t' := by
  have hd' : d < 31 := by simp only [lpWords, List.mem_cons, List.not_mem_nil, or_false] at hd; omega
  refine ⟨fun e he hk => ?_, by
    rw [hm]; exact h.frame.writeW (r := ⟨B, 8 * L⟩) (by simp) _ (Offset.contains_base _ (by omega) (by omega)),
    K.rd.trans h.rd, K.wr.trans h.wr, K.sp.trans h.sp,
    fun x hx h1 h2 => (K.gpr x (not_mem_of_sub hr h2)).trans (h.cs x hx h1 h2)⟩
  rw [← h.hdr e he hk, hm]
  exact writeW_outside t.mem B (d := 8 * d) v (by omega) |>.word (hk d hd) (by omega)

/-- Whether `hK` octets are left: `rand_len − used ≥ hK`. -/
theorem avail_ok {t : State} {B : Addr} {Z rl u w : Nat} (hs : Scr t B Z) (h31 : t.gpr .r31 = B) (hZ : 256 ≤ Z)
    (hrl : word t.mem B (8 * hRandLen) = BitVec.ofNat 64 rl) (hu : word t.mem B (8 * hUsed) = BitVec.ofNat 64 u)
    (hk : word t.mem B (8 * hK) = BitVec.ofNat 64 (8 * w)) (hul : u ≤ rl) (hrl' : rl < 2 ^ 64) (hw : 8 * w < 2 ^ 63) :
    WP isa (.block ([ldh .r3 hRandLen, ldh .r4 hUsed, .sub .r3 .r3 .r4, ldh .r4 hK] ++ geFlag .r5 .r3 .r4)) t
      fun t' => (t'.gpr .r5 = BitVec.ofNat 64 (if 8 * w ≤ rl - u then 1 else 0) ∧ t'.mem = t.mem) ∧
        Keep [.r3, .r4, .r5, .r0] t t' := by
  have hnw := hs.nowrap
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.r3, .r4] (Q := fun t' => t'.gpr .r3 = BitVec.ofNat 64 rl - BitVec.ofNat 64 u ∧
      t'.gpr .r4 = BitVec.ofNat 64 (8 * w) ∧ t'.mem = t.mem) (by
    simp only [ldh, hRandLen, hUsed, hK] at hrl hu hk ⊢
    prun [h31, hs.ld (d := 144) (n := 8) (by omega), hs.ld (d := 152) (n := 8) (by omega),
      hs.ld (d := 216) (n := 8) (by omega), hrl, hu, hk]) (by decide)) fun t₁ ⟨⟨a3, a4, m₁⟩, k₁⟩ => ?_
  refine WP.mono (geFlag_ok (a3.trans (Offset.ofNat_sub_ofNat hul)) a4 (by omega) hw) fun t₂ ⟨⟨b5, m₂⟩, k₂⟩ => ?_
  exact ⟨⟨b5, m₂.trans m₁⟩, (k₁.trans k₂).mono⟩

/-- The loop's test: `hStat − 4`, zero to go on. -/
theorem tail_ok {t : State} {B : Addr} {Z v : Nat} (hs : Scr t B Z) (h31 : t.gpr .r31 = B) (hZ : 256 ≤ Z)
    (hst : word t.mem B (8 * hStat) = BitVec.ofNat 64 v) (hv : v ≤ 4) :
    WP isa (.block [ldh .r3 hStat, .subi .r3 .r3 4]) t
      fun t' => (isa.eval (.zero .d .r3) t' = some (decide (v = 4)) ∧ t'.mem = t.mem) ∧ Keep [.r3] t t' := by
  have hnw := hs.nowrap
  refine WP.mono (WP.keep [.r3] (Q := fun t' => t'.gpr .r3 = BitVec.ofNat 64 v - BitVec.ofNat 64 4 ∧
      t'.mem = t.mem) (by
    simp only [ldh, hStat] at hst ⊢
    prun [h31, hs.ld (d := 160) (n := 8) (by omega), hst]) (by decide)) fun t' ⟨⟨a3, m⟩, k⟩ => ⟨⟨?_, m⟩, k⟩
  rw [eval_zero, a3]
  rcases (show v = 0 ∨ v = 1 ∨ v = 2 ∨ v = 3 ∨ v = 4 by omega) with rfl | rfl | rfl | rfl | rfl <;> rfl

end VG.Proof.RsaKeyGen.PPC64LE.Cand
