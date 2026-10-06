import VerifiedGarbage.Impl.RsaOaep.AArch64
import VerifiedGarbage.Proof.RsaOaep.Scan
import VerifiedGarbage.Proof.RsaOaep.Mask
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.Call
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.Covers
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.GetElem

/-!
# RSAES-OAEP on AArch64: the frame and the working space

As on x86-64 (`Proof/RsaOaep/X86_64/Basic.lean`): `F` is `sp` in the inner
frame, whose `frameBytes` bytes are writable, and `S` the working space,
of which the first `oRsa` bytes are ours, in its slot; the 16 bytes a call
of a streaming hash function uses are just below `F` (`Lay`). `Rep m F S V W`
views memory as functions: byte `o` of our working space is `V o`, word `k`
of the frame `W k`; a store to either changes the one function at what it
writes (`Rep.wb`, `Rep.wf`), and code that writes only ranges of our
working space and below the frame keeps the rest (`Rep.frame`).
-/

namespace VG.Proof.RsaOaep.AArch64

open VG VG.AArch64 VG.Impl.RsaOaep.AArch64
open VG.Proof.Mgf1 (ifp ifn)

/-- `p + d`. -/
abbrev off (p : Addr) (d : Nat) : Addr := p + BitVec.ofNat 64 d

/-- The word at `p + d`. -/
abbrev word (m : Mem) (p : Addr) (d : Nat) : BitVec 64 := m.readW (off p d) 64

theorem off_off (p : Addr) (a b : Nat) : off (off p a) b = off p (a + b) := by
  simp only [off, BitVec.add_assoc, BitVec.ofNat_add]

/-- The 16 bytes below `F` that a call of a streaming hash function uses. -/
abbrev retR (F : Addr) : Region := below F 16

/-- The frame's words. -/
def nW : Nat := frameBytes / 8

/-- Where the frame and the working space are. -/
structure Geo (F S : Addr) : Prop where
  F16 : 16 ≤ F.toNat
  Fw : F.toNat + frameBytes ≤ 2 ^ 64
  Sw : S.toNat + oRsa ≤ 2 ^ 64
  dFS : Region.Disjoint ⟨F, frameBytes⟩ ⟨S, oRsa⟩
  dRS : Region.Disjoint (retR F) ⟨S, oRsa⟩
  dRF : Region.Disjoint (retR F) ⟨F, frameBytes⟩

/-- The state in the frame `F`, with the working space `S` in its slot. -/
structure Lay (t : State) (F S : Addr) : Prop where
  sp : t.sp = F
  fr : Covers [⟨F, frameBytes⟩] t.wr
  sc : Covers [⟨S, oRsa⟩] t.wr
  slot : word t.mem F sScr = S
  geo : Geo F S

theorem cF (F : Addr) {d n : Nat} (h : d + n ≤ frameBytes) : Region.Contains ⟨F, frameBytes⟩ (off F d) n :=
  Offset.contains_base F h (by unfold frameBytes at *; omega)

theorem cS (S : Addr) {o n : Nat} (h : o + n ≤ oRsa) : Region.Contains ⟨S, oRsa⟩ (off S o) n :=
  Offset.contains_base S h (by unfold oRsa at *; omega)

namespace Lay

variable {t : State} {F S : Addr} (L : Lay t F S)
include L

/-- Bytes of the frame are writable, and readable. -/
theorem st {d n : Nat} (h : d + n ≤ frameBytes) : InRegions t.wr (off F d) n :=
  L.fr _ _ ⟨_, List.mem_singleton_self _, cF F h⟩

theorem ld {d n : Nat} (h : d + n ≤ frameBytes) : InRegions (t.rd ++ t.wr) (off F d) n :=
  let ⟨r, hr, hc⟩ := L.st h
  ⟨r, List.mem_append_right _ hr, hc⟩

/-- Bytes of our working space are writable, and readable. -/
theorem sst {o n : Nat} (h : o + n ≤ oRsa) : InRegions t.wr (off S o) n :=
  L.sc _ _ ⟨_, List.mem_singleton_self _, cS S h⟩

theorem sld {o n : Nat} (h : o + n ≤ oRsa) : InRegions (t.rd ++ t.wr) (off S o) n :=
  let ⟨r, hr, hc⟩ := L.sst h
  ⟨r, List.mem_append_right _ hr, hc⟩

/-- A range of our working space is writable. -/
theorem cov {o n : Nat} (h : o + n ≤ oRsa) : Covers [⟨off S o, n⟩] t.wr :=
  Covers.trans (Covers.of_sub fun r hr => by
    rw [List.mem_singleton.mp hr]
    exact ⟨_, List.mem_singleton_self _, o, rfl, by simp only; omega⟩) L.sc

/-- `Lay` holds of a state with the same stack pointer and regions and the
same slot of `scratch`. -/
theorem congr {t' : State} (hsp : t'.sp = t.sp) (hwr : t'.wr = t.wr)
    (hs : word t'.mem F sScr = word t.mem F sScr) : Lay t' F S :=
  ⟨hsp.trans L.sp, hwr ▸ L.fr, hwr ▸ L.sc, hs.trans L.slot, L.geo⟩

/-- A range of our working space and the 16 bytes below the frame are apart. -/
theorem stk {o n : Nat} (h : o + n ≤ oRsa) : (below t.sp 16).Disjoint ⟨off S o, n⟩ := by
  rw [L.sp]; exact L.geo.dRS.sub_right (Offset.sub_base S h)

theorem sp16 : 16 ≤ t.sp.toNat := by rw [L.sp]; exact L.geo.F16

end Lay

/-- Two ranges of our working space that do not overlap. -/
theorem sdis (S : Addr) {a n b k : Nat} (h : a + n ≤ b ∨ b + k ≤ a) (ha : a + n ≤ oRsa) (hb : b + k ≤ oRsa) :
    Region.Disjoint ⟨off S a, n⟩ ⟨off S b, k⟩ :=
  Offset.disjoint S h (by unfold oRsa at ha; omega) (by unfold oRsa at hb; omega)

/-! ## The working space and the frame, as functions -/

/-- `f` with the value at `a` replaced by `v`. -/
def upd {α : Type} (f : Nat → α) (a : Nat) (v : α) : Nat → α := fun x => if x = a then v else f x

structure Rep (m : Mem) (F S : Addr) (V : Nat → Byte) (W : Nat → BitVec 64) : Prop where
  scr : ∀ o < oRsa, m (off S o) = V o
  fr : ∀ k < nW, word m F (8 * k) = W k

/-- Whether `o` is in one of the ranges `rgs` of offsets. -/
def inR (rgs : List (Nat × Nat)) (o : Nat) : Prop := ∃ p ∈ rgs, p.1 ≤ o ∧ o < p.1 + p.2

instance (rgs : List (Nat × Nat)) (o : Nat) : Decidable (inR rgs o) :=
  inferInstanceAs (Decidable (∃ p ∈ rgs, p.1 ≤ o ∧ o < p.1 + p.2))

/-- The regions of the ranges `rgs` of our working space. -/
def regs (S : Addr) (rgs : List (Nat × Nat)) : List Region := rgs.map fun p => ⟨off S p.1, p.2⟩

theorem Geo.dRS' {F S : Addr} (G : Geo F S) {o : Nat} (ho : o < oRsa) : ¬ (retR F).Contains (off S o) 1 :=
  fun hc => G.dRS _ hc ((cS S (o := o) (n := 1) (by omega)).byte (by rw [BitVec.sub_self]; decide))

theorem Geo.cFw {F S : Addr} (_ : Geo F S) {k : Nat} (hk : k < nW) :
    Region.Contains ⟨F, frameBytes⟩ (off F (8 * k)) 8 := cF F (by unfold nW frameBytes at *; omega)

/-- What a callee or a block writing only within the ranges `rgs` of our
working space and below the frame leaves. -/
theorem Rep.frame {m m' : Mem} {F S : Addr} {V : Nat → Byte} {W : Nat → BitVec 64} (G : Geo F S)
    (R : Rep m F S V W) {rgs : List (Nat × Nat)} (hrg : ∀ p ∈ rgs, p.1 + p.2 ≤ oRsa)
    (hF : Frame (regs S rgs ++ [retR F]) m m') :
    Rep m' F S (fun o => if inR rgs o then m' (off S o) else V o) W where
  scr o ho := by
    split
    · rfl
    · rename_i hn
      rw [hF _ fun r hr hc => ?_, R.scr o ho]
      rcases List.mem_append.mp hr with hr | hr
      · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hr
        apply hn
        refine ⟨p, hp, ?_⟩
        have := hrg p hp
        have := (Offset.lt_iff (off S o) S (d := p.1) (n := p.2) (by have := G.Sw; unfold oRsa at *; omega)).mp hc
        rwa [off, Mem.sub_ofNat_toNat S (by unfold oRsa at *; omega)] at this
      · simp only [List.mem_singleton] at hr; subst hr
        exact G.dRS' ho hc
  fr k hk := by
    rw [word, hF.readW (r := ⟨off F (8 * k), 8⟩) (Region.contains_self _ _) (fun r hr => ?_) (by decide)]
    · exact R.fr k hk
    rcases List.mem_append.mp hr with hr | hr
    · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hr
      exact Region.Disjoint.sub_left (Region.Disjoint.sub_right G.dFS (Offset.sub_base S (hrg p hp)))
        (Offset.sub_base F (by unfold nW frameBytes at *; omega))
    · simp only [List.mem_singleton] at hr; subst hr
      exact (G.dRF.sub_right (Offset.sub_base F (by unfold nW frameBytes at *; omega))).symm

/-- A byte written to memory. -/
theorem write1_apply (m : Mem) (a x : Addr) (v : BitVec (8 * 1)) :
    m.write a 1 v x = if x = a then v else m x := by
  simp only [Mem.write]
  by_cases hx : x = a
  · subst hx; simp
  · have : (x - a).toNat ≠ 0 := fun h => hx (by
      have := BitVec.eq_of_toNat_eq (x := x - a) (y := 0) (by simpa using h)
      rw [← BitVec.sub_add_cancel x a, this]; exact BitVec.zero_add _)
    simp only [hx, ite_false]
    exact ite_eq_right_iff.mpr fun h => absurd h (by omega)

/-- A byte store to the working space. -/
theorem Rep.wb {m : Mem} {F S : Addr} {V : Nat → Byte} {W : Nat → BitVec 64} (G : Geo F S)
    (R : Rep m F S V W) {o : Nat} (ho : o < oRsa) (v : Byte) :
    Rep (m.write (off S o) 1 v) F S (upd V o v) W where
  scr x hx := by
    rw [write1_apply, upd]
    by_cases h : x = o
    · subst h; simp
    · rw [ifn (Offset.add_ofNat_ne S (by unfold oRsa at *; omega) (by unfold oRsa at *; omega) h), ifn h,
        R.scr x hx]
  fr k hk := by
    rw [word, Mem.readW, Mem.read_write_sep (Region.Disjoint.sep G.dFS (G.cFw hk) (cS S (o := o) (n := 1) (by omega)))
      (by decide)]
    exact R.fr k hk

/-- A word store to the frame. -/
theorem Rep.wf {m : Mem} {F S : Addr} {V : Nat → Byte} {W : Nat → BitVec 64} (G : Geo F S)
    (R : Rep m F S V W) {k : Nat} (hk : k < nW) (v : BitVec 64) :
    Rep (m.writeW (off F (8 * k)) v) F S V (upd W k v) where
  scr x hx := by
    rw [Mem.writeW, Mem.write_apply (fun h => G.dFS _ ((G.cFw hk).byte h) ((cS S (o := x) (n := 1) (by omega)).byte
      (by rw [BitVec.sub_self]; decide)))]
    exact R.scr x hx
  fr j hj := by
    by_cases h : j = k
    · subst h
      rw [word, Mem.readW_writeW_self64, upd, ifp rfl]
    · rw [word, Mem.readW_writeW_sep (Offset.sep F (by unfold nW frameBytes at *; omega)
        (by unfold nW frameBytes at *; have := G.Fw; omega) (by unfold nW frameBytes at *; have := G.Fw; omega))
        (by decide), upd, ifn h]
      exact R.fr j hj

theorem upd_self {α : Type} (f : Nat → α) (a : Nat) : upd f a (f a) = f := by
  funext x; simp only [upd]; split <;> simp_all

theorem inR_nil (o : Nat) : ¬ inR [] o := by simp [inR]

theorem inR_cons (a n : Nat) (rgs : List (Nat × Nat)) (o : Nat) :
    inR ((a, n) :: rgs) o ↔ (a ≤ o ∧ o < a + n) ∨ inR rgs o := by
  simp [inR]

/-! ## Running blocks -/

/-- Runs a block symbolically with `runBlock_cons` and `runStep_some`, the
registers' writes kept folded (`RegUpd`), with the facts `hs`. -/
syntax "oaep_run" " [" Lean.Parser.Tactic.simpLemma,* "]" : tactic
macro_rules
  | `(tactic| oaep_run [$hs,*]) => `(tactic| (apply WP.of_runBlock; simp only [List.cons_append, List.nil_append,
      runBlock_cons, runStep_some, runBlock_nil, exec, State.read, State.load, State.store, addr, Size.bits,
      Size.bytes, BitVec.setWidth_eq, Nat.reduceMul, Nat.reduceMod, Nat.reduceLT, Nat.reduceAdd, and_self,
      ite_true, ite_false, reduceCtorEq, Option.map_some, Option.bind_some, Option.some.injEq, exists_eq_left',
      RegUpd.gpr_write, RegUpd.rd_write, RegUpd.wr_write, RegUpd.sp_write, RegUpd.mem_write, RegUpd.v_write,
      $hs,*]))

/-! ## Masks -/

/-- `sbc r, r, r` after `subs _, a, b`: the borrow of `a - b`, as a mask. -/
theorem sbc_self (r a b : BitVec 64) :
    r + ~~~r + BitVec.ofNat 64 (decide (2 ^ 64 ≤ a.toNat + (~~~b).toNat + true.toNat)).toNat =
      if b.toNat ≤ a.toNat then 0 else BitVec.allOnes 64 := by
  have hn : r + ~~~r = BitVec.allOnes 64 := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, BitVec.toNat_not, BitVec.toNat_allOnes]
    have := r.isLt
    rw [Nat.mod_eq_of_lt (by omega)]; omega
  have hb : (~~~b).toNat = 2 ^ 64 - 1 - b.toNat := BitVec.toNat_not
  have := b.isLt
  rw [hn, hb]
  by_cases h : b.toNat ≤ a.toNat
  · rw [show decide (2 ^ 64 ≤ a.toNat + (2 ^ 64 - 1 - b.toNat) + true.toNat) = true by
      simp only [Bool.toNat_true, decide_eq_true_eq]; omega]
    simp only [h, ↓reduceIte]; rfl
  · rw [show decide (2 ^ 64 ≤ a.toNat + (2 ^ 64 - 1 - b.toNat) + true.toNat) = false by
      simp only [Bool.toNat_true, decide_eq_false_iff_not]; omega]
    simp only [h, ↓reduceIte]; rfl

/-- The borrow of `x - 1`: all ones iff `x = 0`. -/
theorem sbc_one (r x : BitVec 64) :
    r + ~~~r + BitVec.ofNat 64 (decide (2 ^ 64 ≤ x.toNat + (~~~(1 : BitVec 64)).toNat + true.toNat)).toNat =
      zM x := by
  rw [sbc_self]
  by_cases h : x = 0
  · subst h; rfl
  · have : (1 : BitVec 64).toNat ≤ x.toNat := by
      have : x.toNat ≠ 0 := fun e => h (BitVec.eq_of_toNat_eq e)
      show 1 ≤ x.toNat; omega
    rw [ifp this, zM, ifn h]

end VG.Proof.RsaOaep.AArch64
