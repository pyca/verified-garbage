module

public import VerifiedGarbage.Proof.CmacTripleDes.StreamScratch
public import VerifiedGarbage.TCB.PPC64LE.Target
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Spec.Cmac.TripleDesContract
import VerifiedGarbage.Proof.Framework.PPC64LE.Call
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.TripleDes.PPC64LE.Ecb.Call
import VerifiedGarbage.Proof.TripleDes.Schedule
import VerifiedGarbage.Proof.TripleDes.CbcBlocks
public import VerifiedGarbage.Proof.CmacTripleDes.Stream
import VerifiedGarbage.Proof.CmacTripleDes.Cmac
public import VerifiedGarbage.Proof.CmacTripleDes.Block
public import VerifiedGarbage.Proof.Framework.PPC64LE.Step
public import VerifiedGarbage.Proof.Cmac.Mem
public import VerifiedGarbage.Proof.CmacTripleDes.Bytes
public import VerifiedGarbage.Impl.CmacTripleDes.Stream.PPC64LE
public import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Proof.Framework.Semantics
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Cmac.Stream
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.TCB.Code
public import VerifiedGarbage.Spec.Cmac
import VerifiedGarbage.Proof.Cmac.Spec
import VerifiedGarbage.Proof.Framework.PPC64LE.ByteStep
import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.Framework.GetElem
public import VerifiedGarbage.Impl.StackScratch.PPC64LE
import VerifiedGarbage.Proof.Framework.PPC64LE.StackScratch
public import VerifiedGarbage.TCB.PPC64LE.Isa
import VerifiedGarbage.Proof.Framework.Covers
import VerifiedGarbage.Proof.TripleDes.PPC64LE.Key.Verified
import VerifiedGarbage.Proof.Gcm.Bits
public import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
public import VerifiedGarbage.Proof.TripleDes.PPC64LE.ConstantTime
import VerifiedGarbage.Proof.CmacTripleDes.Stream.PPC64LE.Lit
import VerifiedGarbage.Proof.TripleDes.PPC64LE.FunctionsLit
import VerifiedGarbage.Proof.Framework.PPC64LE.Lit
meta import VerifiedGarbage.Proof.CmacTripleDes.Stream.PPC64LE.Lit
meta import VerifiedGarbage.Proof.TripleDes.PPC64LE.FunctionsLit
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Lit
meta import VerifiedGarbage.Impl.CmacTripleDes.Stream.PPC64LE
meta import VerifiedGarbage.Proof.Framework.RegSet

/-! ### `CmacTripleDes.Stream.PPC64LE.CT`, which only this module used -/

section

/-!
# Streaming TDEA-CMAC on PPC64LE is constant time

Only the pointers, `count`, `len` and `key_len` are public: `r3`–`r6`, and
`r7` for `absorb`. The key expansion and the block function are analysed at
their calls; the block function never writes `r29`–`r31`, which hold what
`absorb` counts across its calls, nor `r3`–`r5`.
-/

@[expose] public section

namespace VG.Proof.CmacTripleDes.Stream.PPC64LE

open VG VG.PPC64LE VG.Impl.CmacTripleDes.Stream.PPC64LE

/-- The public arguments of `stream_init` and `finish`, and of `absorb`. -/
abbrev pub4 : State → State → Prop := Proof.TripleDes.PPC64LE.PublicRegs [.r3, .r4, .r5, .r6]
abbrev pub5 : State → State → Prop := Proof.TripleDes.PPC64LE.PublicRegs [.r3, .r4, .r5, .r6, .r7]

theorem init_ct (pre : State → Prop) : ConstantTime isa pre pub4 streamInit :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.r3, .r4, .r5, .r6])
    (fun _ _ _ _ hp => ⟨hp.1, fun r hr => hp.2 r (Taint.mem_ofRegs.mp hr)⟩) (by taint_decide)

theorem absorb_ct (pre : State → Prop) : ConstantTime isa pre pub5 absorb :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.r3, .r4, .r5, .r6, .r7])
    (fun _ _ _ _ hp => ⟨hp.1, fun r hr => hp.2 r (Taint.mem_ofRegs.mp hr)⟩) (by taint_decide)

theorem finish_ct (pre : State → Prop) : ConstantTime isa pre pub4 finish :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.r3, .r4, .r5, .r6])
    (fun _ _ _ _ hp => ⟨hp.1, fun r hr => hp.2 r (Taint.mem_ofRegs.mp hr)⟩) (by taint_decide)

end VG.Proof.CmacTripleDes.Stream.PPC64LE

end

end

/-! ### `CmacTripleDes.Stream.PPC64LE.Calls`, which only this module used -/

section

/-! ### `CmacTripleDes.Stream.PPC64LE.Common`, which this module and modules that import it used -/

section

/-!
# Streaming TDEA-CMAC on PPC64LE: what the functions share

The weakest preconditions of the instructions `Framework/PPC64LE/Step.lean`
lacks (`mflr`, `mtlr`, `or`, `ldbrx`, `stdbrx`), the doubling of `dblCode`
(`dblCode_wp`), and that a word is determined by its bytes (`le8_inj`).
-/

@[expose] public section

namespace VG.Proof.CmacTripleDes.Stream.PPC64LE

open VG VG.PPC64LE VG.Impl.CmacTripleDes.Stream.PPC64LE
open VG.Proof.Cmac (le8)

section
variable {is : List Instr} {s : State} {Q : State → Prop}

theorem wp_mflr {d : Reg} (k : ∀ s', Upd s s' d s.lr → WP isa (.block is) s' Q) :
    WP isa (.block (.mflr d :: is)) s Q :=
  WP.cons exec_mflr (k _ (Upd.write _ _ _))

theorem wp_mtlr {r : Reg} (k : WP isa (.block is) { s with lr := s.gpr r } Q) :
    WP isa (.block (.mtlr r :: is)) s Q :=
  WP.cons exec_mtlr k

theorem wp_or {d n m : Reg} (k : ∀ s', Upd s s' d (s.gpr n ||| s.gpr m) → WP isa (.block is) s' Q) :
    WP isa (.block (.logic .or d n m :: is)) s Q :=
  WP.cons exec_logic (k _ (Upd.write _ _ _))

/-- `ldbrx t, a, b`. -/
theorem wp_ldbrx {t a b : Reg} {ea : Addr} (hn : a ≠ .r0) (hea : s.gpr a + s.gpr b = ea)
    (hin : InRegions (s.rd ++ s.wr) ea 8)
    (k : ∀ s', Upd s s' t (rev64 (s.mem.readW ea 64)) → WP isa (.block is) s' Q) :
    WP isa (.block (.loadRev .d t a b :: is)) s Q := by
  refine WP.cons (s' := s.write t (rev64 (s.mem.readW ea 64))) ?_ (k _ (Upd.write _ _ _))
  rw [exec_loadRev_d hn (by rw [hea]; exact hin), hea]

/-- `stdbrx t, a, b`. -/
theorem wp_stdbrx {t a b : Reg} {ea : Addr} (hn : a ≠ .r0) (hea : s.gpr a + s.gpr b = ea)
    (hout : InRegions s.wr ea 8)
    (k : ∀ s', Mupd s s' (s.mem.writeW ea (rev64 (s.gpr t))) → WP isa (.block is) s' Q) :
    WP isa (.block (.storeRev .d t a b :: is)) s Q := by
  refine WP.cons (s' := { s with mem := s.mem.writeW ea (rev64 (s.gpr t)) }) ?_ (k _ ⟨rfl, rfl, rfl, rfl⟩)
  rw [exec_storeRev_d hn (by rw [hea]; exact hout), hea]

end

/-- A slot of the working space at `B` is writable. -/
theorem scr_in {s : State} {B : Addr} {off : Nat} (hw : (⟨B, 640⟩ : Region) ∈ s.wr) (h : off + 8 ≤ 640) :
    InRegions s.wr (B + BitVec.ofNat 64 off) 8 :=
  ⟨_, hw, VG.Offset.contains_base _ h (by omega_using [h])⟩

theorem scr_rd {s : State} {B : Addr} {off : Nat} (hw : (⟨B, 640⟩ : Region) ∈ s.wr) (h : off + 8 ≤ 640) :
    InRegions (s.rd ++ s.wr) (B + BitVec.ofNat 64 off) 8 :=
  let ⟨r, hr, hc⟩ := scr_in hw h
  ⟨r, List.mem_append_right _ hr, hc⟩

/-- A word read past a word written apart from it. -/
theorem readW_sep64 {m : Mem} {a b : Addr} {v : BitVec 64} (h : Region.Disjoint ⟨a, 8⟩ ⟨b, 8⟩) :
    (m.writeW b v).readW a 64 = m.readW a 64 :=
  Mem.readW_writeW_sep (fun x h1 h2 => h x (by simp only [Region.Contains]; omega_using [h1])
    (by simp only [Region.Contains]; omega_using [h2])) (by decide)

/-- The registers the functions use as temporaries are not preserved. -/
theorem preserved_ne : ∀ r ∈ preserved, r ≠ .r0 ∧ r ≠ .r3 ∧ r ≠ .r4 ∧ r ≠ .r5 ∧ r ≠ .r6 ∧ r ≠ .r7 ∧
    r ≠ .r8 ∧ r ≠ .r9 ∧ r ≠ .r10 ∧ r ≠ .r11 ∧ r ≠ .r12 := by decide

theorem rev64_eq (x : BitVec 64) : rev64 x = byteRev64 x := rfl

theorem rev64_rev64 (x : BitVec 64) : rev64 (rev64 x) = x := Proof.Gcm.byteRev64_byteRev64 x

theorem le8_inj {a b : BitVec 64} (h : le8 a = le8 b) : a = b := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  have e := congrArg (fun l => (l.getD (i / 8) 0).getLsbD (i % 8)) h
  simp only [Proof.Cmac.getD_le8 _ (show i / 8 < 8 by omega_using [hi]), BitVec.getLsbD_extractLsb',
    show i % 8 < 8 by omega_using [], decide_true, Bool.true_and, show 8 * (i / 8) + i % 8 = i by omega_using []] at e
  exact e

/-- The doubling as `dblCode` computes it. -/
theorem dbl_eq (y : BitVec 64) :
    (y <<< 1) ^^^ ((0 - (y >>> 63)) &&& BitVec.ofNat 64 0x1b) = dbl64 y := by
  rw [msb_shift, dbl64]
  by_cases hm : y.msb
  · rw [ite_eq_left hm, ite_eq_left hm]; congr 1
  · rw [ite_eq_right hm, ite_eq_right hm]; congr 1

/-- `dblCode` doubles `r7`, with `r6 = 0`, writing `r8`–`r10`. -/
theorem dblCode_wp {s : State} {is : List Instr} {Q : State → Prop} (h6 : s.gpr .r6 = 0)
    (k : ∀ s', s'.gpr .r7 = dbl64 (s.gpr .r7) →
      (∀ r, r ≠ .r7 → r ≠ .r8 → r ≠ .r9 → r ≠ .r10 → s'.gpr r = s.gpr r) → s'.mem = s.mem →
      s'.rd = s.rd → s'.wr = s.wr → WP isa (.block is) s' Q) :
    WP isa (.block (dblCode ++ is)) s Q := by
  simp only [dblCode, List.cons_append, List.nil_append]
  refine wp_lsr (by decide) fun s₁ u₁ => wp_sub fun s₂ u₂ => wp_li (by decide) fun s₃ u₃ =>
    wp_and fun s₄ u₄ => wp_lsl (by decide) fun s₅ u₅ => wp_xor fun s₆ u₆ => ?_
  refine k s₆ ?_ (fun r h7 h8 h9 h10 => ?_) (by rw [u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem])
    (by rw [u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd]) (by rw [u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr])
  · have a5 : s₅.gpr .r7 = s.gpr .r7 <<< 1 := by
      rw [u₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide)]
    have b3 : s₃.gpr .r9 = 0 - (s.gpr .r7 >>> 63) := by
      rw [u₃.other _ (by decide), u₂.gpr, u₁.gpr, u₁.other _ (by decide), h6]
      rfl
    have b5 : s₅.gpr .r9 = (0 - (s.gpr .r7 >>> 63)) &&& BitVec.ofNat 64 0x1b := by
      rw [u₅.other _ (by decide), u₄.gpr, u₃.gpr, b3]
    rw [u₆.gpr, a5, b5, dbl_eq]
  · rw [u₆.other r h7, u₅.other r h7, u₄.other r h9, u₃.other r h10, u₂.other r h9, u₁.other r h8]

/-- `(n - 1) & 7`, plus one. -/
theorem held_word {n : Nat} (hn : n < 2 ^ 64) (h0 : n ≠ 0) :
    (BitVec.ofNat 64 n - BitVec.ofNat 64 1 &&& BitVec.ofNat 64 7) + BitVec.ofNat 64 1 =
      BitVec.ofNat 64 ((n - 1) % 8 + 1) := by
  apply BitVec.eq_of_toNat_eq
  have e1 : (BitVec.ofNat 64 n - BitVec.ofNat 64 1).toNat = n - 1 := by
    rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat]; omega_using [hn, h0]
  rw [BitVec.toNat_add, BitVec.toNat_and, e1, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    show (7 : Nat) % 2 ^ 64 = 2 ^ 3 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod, BitVec.toNat_ofNat]

/-- `heldCode` computes, from `count = n` in `r4`, the number of bytes held
back for a message of `n` bytes, to `r8`, through `r9`. -/
theorem heldCode_wp {s : State} {n : Nat} (hn : n < 2 ^ 64) (h4 : s.gpr .r4 = BitVec.ofNat 64 n)
    {Q : State → Prop}
    (k : ∀ t, t.gpr .r8 = BitVec.ofNat 64 (Proof.CmacTripleDes.Stream.held n) →
      (∀ r, r ≠ .r8 → r ≠ .r9 → t.gpr r = s.gpr r) → t.mem = s.mem → t.rd = s.rd → t.wr = s.wr → Q t) :
    WP isa heldCode s Q := by
  by_cases h0 : n = 0
  · subst h0
    refine WP.ite true (by rw [eval_zero_ofNat s .r4 (by decide) h4]; rfl) (fun _ => ?_) (fun h => by cases h)
    refine wp_li (by decide) fun t u => wp_nil (k t (by rw [u.gpr]; rfl) (fun r h8 _ => u.other r h8) u.mem u.rd u.wr)
  refine WP.ite false (by rw [eval_zero_ofNat s .r4 hn h4]; simp [h0]) (fun h => by cases h) fun _ => ?_
  refine wp_subi (by decide) (by decide) fun t₁ u₁ => wp_li (by decide) fun t₂ u₂ => wp_and fun t₃ u₃ =>
    wp_addi (by decide) (by decide) fun t₄ u₄ => wp_nil ?_
  refine k t₄ ?_ (fun r h8 h9 => by rw [u₄.other r h8, u₃.other r h8, u₂.other r h9, u₁.other r h8])
    (by rw [u₄.mem, u₃.mem, u₂.mem, u₁.mem]) (by rw [u₄.rd, u₃.rd, u₂.rd, u₁.rd]) (by rw [u₄.wr, u₃.wr, u₂.wr, u₁.wr])
  rw [u₄.gpr, u₃.gpr, u₂.gpr, u₂.other _ (by decide), u₁.gpr, h4, Proof.CmacTripleDes.Stream.held_pos (by omega_using [h0])]
  exact held_word hn h0

end VG.Proof.CmacTripleDes.Stream.PPC64LE

end

end

/-!
# Streaming TDEA-CMAC on PPC64LE: the calls

`keyCall_wp` and `encCall_wp`: the calls of the verified key expansion and
block function, from their contracts (`Key.correct`, `Ecb.call_ok`), as the
streaming functions make them: the key expansion writes the schedule at the
start of the state, and the block function enciphers the block at `B + 512`
with the working space at `B`, the scratch buffer's 640 bytes.
-/

@[expose] public section

namespace VG.Proof.CmacTripleDes.Stream.PPC64LE

open VG VG.PPC64LE VG.Impl.CmacTripleDes.Stream.PPC64LE

/-- The key expansion's call, with the key at `r3` (`len` bytes, in `r4`)
and the schedule at `r5`, within the 416 bytes at `S`. -/
theorem keyCall_wp {s : State} {K S : Addr} {len : Nat} (h3 : s.gpr .r3 = K) (h4 : s.gpr .r4 = BitVec.ofNat 64 len)
    (h5 : s.gpr .r5 = S) (hlen : len < 2 ^ 64) (hkey : (⟨K, len⟩ : Region) ∈ s.rd)
    (hS : (⟨S, 416⟩ : Region) ∈ s.wr) (hd : Region.Disjoint ⟨K, len⟩ ⟨S, 416⟩)
    (hv : Spec.TripleDes.validKey len) {Q : State → Prop}
    (k : ∀ s', s'.rd = s.rd → s'.wr = s.wr → Frame [⟨S, 384⟩] s.mem s'.mem →
      (∀ r ∈ preserved, s'.gpr r = s.gpr r) →
      Spec.TripleDes.scheduleAt s'.mem S = Spec.TripleDes.expandKey (Spec.TripleDes.bytesAt s.mem K len) → Q s') :
    WP isa keyCall s Q := by
  have c3 := State.callEntry_gpr s (r := .r3) (by decide)
  have c4 := State.callEntry_gpr s (r := .r4) (by decide)
  have c5 := State.callEntry_gpr s (r := .r5) (by decide)
  have hlt : (s.gpr .r4).toNat = len := by rw [h4, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlen]
  have sub : Region.Sub ⟨S, 384⟩ ⟨S, 416⟩ := Region.sub_prefix (by decide)
  refine WP.call (k := Proof.TripleDes.PPC64LE.Key.contract) Proof.TripleDes.PPC64LE.Key.correct
    (rd := [⟨K, len⟩]) (wr := [⟨S, 384⟩]) ?_ ?_ ?_ ?_
  · simp only [Proof.TripleDes.PPC64LE.Key.contract, State.withRegions_gpr, State.withRegions_rd,
      State.withRegions_wr, c3, c4, c5, h3, hlt, h5]
    exact ⟨trivial, trivial, hd.sub_right sub, hv⟩
  · refine VG.Covers.of_sub fun r hr => ?_
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, List.mem_append_left _ hkey, 0, by simp, by simp⟩
    · exact ⟨_, List.mem_append_right _ hS, 0, by simp, by show 0 + 384 ≤ 416; decide⟩
  · refine VG.Covers.of_sub fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    subst hr
    exact ⟨_, hS, 0, by simp, by show 0 + 384 ≤ 416; decide⟩
  · intro s' rd wr _ frame callee _ out
    simp only [Proof.TripleDes.PPC64LE.Key.contract, State.withRegions_gpr, State.withRegions_mem,
      State.callEntry_mem, c3, c4, c5, h3, hlt, h5] at out
    exact k s' rd wr frame callee out

/-- The block function's call, with the schedule at `r3 = S`, the block at
`r4 = B + 512` and the working space at `r5 = B`. -/
theorem encCall_wp {s : State} {S B : Addr} (h3 : s.gpr .r3 = S) (h4 : s.gpr .r4 = B + BitVec.ofNat 64 512)
    (h5 : s.gpr .r5 = B) (hkey : InRegions (s.rd ++ s.wr) S 384) {L : Nat} (hB : (⟨B, L⟩ : Region) ∈ s.wr)
    (hL : 640 ≤ L) (hd : Region.Disjoint ⟨S, 384⟩ ⟨B, 640⟩) {Q : State → Prop}
    (k : ∀ s', s'.rd = s.rd → s'.wr = s.wr → (∀ r ∈ preserved, s'.gpr r = s.gpr r) →
      s'.gpr .r3 = S → s'.gpr .r4 = B + BitVec.ofNat 64 512 → s'.gpr .r5 = B →
      Frame [⟨B, 520⟩] s.mem s'.mem →
      Spec.TripleDes.blockAt s'.mem (B + BitVec.ofNat 64 512) =
        Spec.TripleDes.encryptBlock (Spec.TripleDes.scheduleAt s.mem S)
          (Spec.TripleDes.blockAt s.mem (B + BitVec.ofNat 64 512)) → Q s') :
    WP isa encCall s Q := by
  have bufIn : Region.Sub ⟨B + BitVec.ofNat 64 512, 8⟩ ⟨B, 640⟩ := VG.Offset.sub_base _ (by decide)
  have scrIn : Region.Sub ⟨B, 512⟩ ⟨B, 640⟩ := Region.sub_prefix (by decide)
  have cw : VG.Covers [⟨s.gpr .r4, 8⟩, ⟨s.gpr .r5, 512⟩] s.wr := VG.Covers.of_sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨⟨B, L⟩, hB, 512, h4, by show 512 + 8 ≤ L; omega_using [hL]⟩
    · exact ⟨⟨B, L⟩, hB, 0, by simp [h5], by show 0 + 512 ≤ L; omega_using [hL]⟩
  have hp : Proof.TripleDes.PPC64LE.Ecb.CallPre s :=
    ⟨VG.Covers.cons (by rw [h3]; exact VG.Covers.one hkey) (VG.Covers.right cw), cw,
      by rw [h3, h5]; exact hd.sub_right scrIn,
      by rw [h4, h5]; exact VG.Offset.disjoint_base _ (by decide) (by omega_using [])⟩
  refine WP.mono (Proof.TripleDes.PPC64LE.Ecb.call_ok .encrypt s hp) fun s' h' => ?_
  have sub : ∀ r ∈ [(⟨s.gpr .r4, 8⟩ : Region), ⟨s.gpr .r5, 512⟩], ∃ r' ∈ [(⟨B, 520⟩ : Region)], Region.Sub r r' :=
    fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨_, List.mem_singleton_self _, by rw [h4]; exact VG.Offset.sub_base _ (by decide)⟩
      · exact ⟨_, List.mem_singleton_self _, by rw [h5]; exact Region.sub_prefix (by decide)⟩
  have out := h'.output
  rw [h3, h4] at out
  exact k s' h'.rd h'.wr h'.callee (by rw [h'.reg _ (by decide), h3]) (by rw [h'.reg _ (by decide), h4])
    (by rw [h'.reg _ (by decide), h5]) (h'.mem.sub sub) out

end VG.Proof.CmacTripleDes.Stream.PPC64LE

end

end

/-! ### `CmacTripleDes.Stream.PPC64LE.Copy`, which only this module used -/

section

/-!
# Streaming TDEA-CMAC on PPC64LE: the byte copy

`copyLoop_wp`: `copyLoop` copies the `n` bytes at `src` (`r10`) to `dst`
(`r11`), where `r12 = n`, when the two do not overlap, and changes no other
memory and no register but `r0` and `r10`–`r12`, leaving `r10` and `r11`
past the bytes.
-/

@[expose] public section

namespace VG.Proof.CmacTripleDes.Stream.PPC64LE

open VG VG.PPC64LE VG.Impl.CmacTripleDes.Stream.PPC64LE

theorem sub_lt_one {x a : Addr} : (x - a).toNat < 1 ↔ x = a := by
  constructor
  · intro h
    have h0 : x - a = 0 := BitVec.eq_of_toNat_eq (by show _ = 0; omega_using [h])
    calc x = x - a + a := (BitVec.sub_add_cancel x a).symm
      _ = a := by rw [h0]; simp
  · rintro rfl; simp

theorem ofNat_succ (p : Addr) (j : Nat) :
    p + BitVec.ofNat 64 j + BitVec.ofNat 64 1 = p + BitVec.ofNat 64 (j + 1) := by
  rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat]

/-- After `j` of the `n` bytes. -/
structure CopyInv (s : State) (src dst : Addr) (n j : Nat) (t : State) : Prop where
  r10 : t.gpr .r10 = src + BitVec.ofNat 64 j
  r11 : t.gpr .r11 = dst + BitVec.ofNat 64 j
  r12 : t.gpr .r12 = BitVec.ofNat 64 (n - j)
  regs : ∀ r, r ≠ .r0 → r ≠ .r10 → r ≠ .r11 → r ≠ .r12 → t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  copied : ∀ i < j, t.mem (dst + BitVec.ofNat 64 i) = s.mem (src + BitVec.ofNat 64 i)
  rest : ∀ x, (∀ i < j, x ≠ dst + BitVec.ofNat 64 i) → t.mem x = s.mem x

theorem copy_step {s : State} {src dst : Addr} {n j : Nat} (hj : j < n) (hn : n < 2 ^ 64)
    (hrd : ∀ i < n, InRegions (s.rd ++ s.wr) (src + BitVec.ofNat 64 i) 1)
    (hwr : ∀ i < n, InRegions s.wr (dst + BitVec.ofNat 64 i) 1)
    (hsep : ∀ i < n, ∀ i' < n, src + BitVec.ofNat 64 i ≠ dst + BitVec.ofNat 64 i')
    {t : State} (hI : CopyInv s src dst n j t) :
    WP isa (.block [.lbz .r0 .r10 0, .stb .r0 .r11 0, .addi .r10 .r10 1, .addi .r11 .r11 1,
      .subi .r12 .r12 1]) t (CopyInv s src dst n (j + 1)) := by
  refine wp_lbz (a := src + BitVec.ofNat 64 j) (by decide) (by decide) (by rw [hI.r10]; simp)
    (by rw [hI.rd, hI.wr]; exact hrd j hj) fun t₁ u₁ => ?_
  refine wp_stb (a := dst + BitVec.ofNat 64 j) (by decide) (by decide)
    (by rw [u₁.other _ (by decide), hI.r11]; simp) (by rw [u₁.wr, hI.wr]; exact hwr j hj) fun t₂ u₂ => ?_
  refine wp_addi (by decide) (by decide) fun t₃ u₃ => wp_addi (by decide) (by decide) fun t₄ u₄ =>
    wp_subi (by decide) (by decide) fun t₅ u₅ => wp_nil ?_
  have src_j : t.mem (src + BitVec.ofNat 64 j) = s.mem (src + BitVec.ofNat 64 j) :=
    hI.rest _ fun i hi => hsep j hj i (by omega_using [hj, hi])
  have m₅ : t₅.mem = t.mem.writeW (dst + BitVec.ofNat 64 j) (s.mem (src + BitVec.ofNat 64 j)) := by
    rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.gpr, u₁.mem, setWidth8_64, src_j]
  refine ⟨?_, ?_, ?_, fun r h0 h10 h11 h12 => ?_, by rw [u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd, hI.rd],
    by rw [u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr, hI.wr], fun i hi => ?_, fun x hx => ?_⟩
  · rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, u₂.gpr, u₁.other _ (by decide), hI.r10,
      ofNat_succ]
  · rw [u₅.other _ (by decide), u₄.gpr, u₃.other _ (by decide), u₂.gpr, u₁.other _ (by decide), hI.r11,
      ofNat_succ]
  · rw [u₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr, u₁.other _ (by decide), hI.r12]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    omega_using [hj]
  · rw [u₅.other r h12, u₄.other r h11, u₃.other r h10, u₂.gpr, u₁.other r h0, hI.regs r h0 h10 h11 h12]
  · rw [m₅, write1_apply]
    by_cases e : i = j
    · subst e; rw [ite_eq_left (sub_lt_one.mpr rfl)]
    · have hne : dst + BitVec.ofNat 64 i ≠ dst + BitVec.ofNat 64 j := by
        intro h
        have := congrArg (fun y => BitVec.toNat (y - dst)) h
        simp only [VG.Offset.add_sub_cancel_left, BitVec.toNat_ofNat] at this
        rw [Nat.mod_eq_of_lt (by omega_using [hj, hn, hi]), Nat.mod_eq_of_lt (by omega_using [hj, hn])] at this
        exact e this
      rw [ite_eq_right (fun h => hne (sub_lt_one.mp h)), hI.copied i (by omega_using [hi, e])]
  · rw [m₅, write1_apply, ite_eq_right (fun h => hx j (by omega_using []) (sub_lt_one.mp h)),
      hI.rest x fun i hi => hx i (by omega_using [hi])]

theorem copyLoop_wp {s : State} {src dst : Addr} {n : Nat} (hn : n < 2 ^ 64)
    (h10 : s.gpr .r10 = src) (h11 : s.gpr .r11 = dst) (h12 : s.gpr .r12 = BitVec.ofNat 64 n)
    (hrd : ∀ i < n, InRegions (s.rd ++ s.wr) (src + BitVec.ofNat 64 i) 1)
    (hwr : ∀ i < n, InRegions s.wr (dst + BitVec.ofNat 64 i) 1)
    (hsep : ∀ i < n, ∀ i' < n, src + BitVec.ofNat 64 i ≠ dst + BitVec.ofNat 64 i')
    {Q : State → Prop} (k : ∀ t, CopyInv s src dst n n t → Q t) :
    WP isa copyLoop s Q := by
  have h0 : CopyInv s src dst n 0 s := ⟨by rw [h10]; simp, by rw [h11]; simp, by rw [h12, Nat.sub_zero], fun _ _ _ _ _ => rfl,
    rfl, rfl, fun i hi => absurd hi (Nat.not_lt_zero _), fun _ _ => rfl⟩
  by_cases hz : n = 0
  · subst hz
    exact WP.ite true (by rw [eval_zero_ofNat s .r12 (by decide) h12]; rfl) (fun _ => wp_nil (k s h0))
      (fun h => by cases h)
  refine WP.ite false (by rw [eval_zero_ofNat s .r12 hn h12]; simp [hz]) (fun h => by cases h) fun _ => ?_
  refine WP.loop (M := isa) (Q := Q)
    (fun (m : Nat) (t : State) => ∃ j, m = n - j ∧ j < n ∧ CopyInv s src dst n j t) ?_ n s ⟨0, by omega_using [], by omega_using [hz], h0⟩
  rintro _ t ⟨j, rfl, hj, hI⟩
  refine WP.mono (copy_step hj hn hrd hwr hsep hI) fun t' h' => ?_
  have e := eval_nonzero_ofNat' t' .r12 (k := n - (j + 1)) (by omega_using [hn]) h'.r12
  by_cases he : j + 1 = n
  · left; exact ⟨by rw [e]; simp [he], k t' (he ▸ h')⟩
  · right; exact ⟨by rw [e]; simp; omega_using [hj, he], n - (j + 1), by omega_using [hj], j + 1, rfl, by omega_using [hj, he], h'⟩

end VG.Proof.CmacTripleDes.Stream.PPC64LE

end

end

/-! ### `CmacTripleDes.Stream.PPC64LE.Verified`, which only this module used -/

section

/-! ### `CmacTripleDes.Stream.PPC64LE.Init`, which only this module used -/

section

/-!
# Streaming TDEA-CMAC on PPC64LE: `stream_init`

`init_wp`: `streamInit` makes the state represent the empty message under
the key (`Spec.Cmac.tdesRepr`): the key expansion's call writes the
schedule, the block function's call enciphers the zero block, and its
doubling and the doubling of that are the subkeys (`subkeys_tdes`).
-/

@[expose] public section

namespace VG.Proof.CmacTripleDes.Stream.PPC64LE

open VG VG.PPC64LE VG.Impl.CmacTripleDes.Stream.PPC64LE
open VG.Proof.Cmac (le8)

/-- `stream_init`'s precondition, with the working space of 640 bytes at `r6`. -/
structure InitPre (s : State) : Prop where
  rd : s.rd = [⟨s.gpr .r4, (s.gpr .r5).toNat⟩]
  wr : s.wr = [⟨s.gpr .r3, 416⟩, ⟨s.gpr .r6, 640⟩]
  keyState : Region.Disjoint ⟨s.gpr .r4, (s.gpr .r5).toNat⟩ ⟨s.gpr .r3, 416⟩
  keyScr : Region.Disjoint ⟨s.gpr .r4, (s.gpr .r5).toNat⟩ ⟨s.gpr .r6, 640⟩
  stateScr : Region.Disjoint ⟨s.gpr .r3, 416⟩ ⟨s.gpr .r6, 640⟩
  valid : Spec.TripleDes.validKey (s.gpr .r5).toNat
  stateFit : (s.gpr .r3).toNat + 416 ≤ 2 ^ 64
  scrFit : (s.gpr .r6).toNat + 640 ≤ 2 ^ 64

/-- The zero block, as a block. -/
theorem zero_block (m : Mem) (p : Addr) (h : Spec.Aes.bytesAt m p 8 = Spec.Cmac.zeros 8) :
    Spec.TripleDes.blockAt m p = Vector.ofFn fun i => (le8 0).getD i.val 0 := by
  rw [Proof.Cmac.le8_zero, ← h, VG.Proof.TripleDes.ofFn_bytesAt]

/-- `L`, from the block function's output on the zero block. -/
theorem l_eq {m : Mem} {p : Addr} {S : Spec.TripleDes.Schedule}
    (h : Spec.TripleDes.blockAt m p = Spec.TripleDes.encryptBlock S (Vector.ofFn fun i => (le8 0).getD i.val 0)) :
    rev64 (m.readW p 64) = Proof.CmacTripleDes.tdes S 0 := by
  obtain e : le8 (m.readW p 64) = le8 (byteRev64 (Proof.CmacTripleDes.tdes S (byteRev64 0))) := by
    rw [← Proof.CmacTripleDes.tdesWith_le8, Proof.Cmac.le8_readW, VG.Proof.TripleDes.bytesAt_eq, h]
    rfl
  rw [le8_inj e, ← rev64_eq, rev64_rev64]
  rfl


/-- After `initSave`: the return address and the caller's `r30`, `r31` in
the working space, and the key expansion's arguments. -/
structure Saved (s t : State) : Prop where
  r3 : t.gpr .r3 = s.gpr .r4
  r4 : t.gpr .r4 = s.gpr .r5
  r5 : t.gpr .r5 = s.gpr .r3
  r30 : t.gpr .r30 = s.gpr .r6
  r31 : t.gpr .r31 = s.gpr .r3
  regs : ∀ r, r ≠ .r0 → r ≠ .r3 → r ≠ .r4 → r ≠ .r5 → r ≠ .r30 → r ≠ .r31 → t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  mem : t.mem = ((s.mem.writeW (s.gpr .r6 + BitVec.ofNat 64 lrOff) s.lr).writeW
    (s.gpr .r6 + BitVec.ofNat 64 r30Off) (s.gpr .r30)).writeW (s.gpr .r6 + BitVec.ofNat 64 r31Off) (s.gpr .r31)

theorem initSave_wp {s : State} (hp : InitPre s) {is : List Instr} {Q : State → Prop}
    (k : ∀ t, Saved s t → WP isa (.block is) t Q) : WP isa (.block (initSave ++ is)) s Q := by
  obtain hW : (⟨s.gpr .r6, 640⟩ : Region) ∈ s.wr := by rw [hp.wr]; simp
  simp only [initSave, mr, List.cons_append, List.nil_append]
  refine wp_mflr fun s₁ u₁ => ?_
  refine wp_std (a := s.gpr .r6 + BitVec.ofNat 64 lrOff) (by decide) (by decide) (by rw [u₁.other _ (by decide)])
    (by rw [u₁.wr]; exact scr_in hW (by decide)) fun s₂ u₂ => ?_
  refine wp_std (a := s.gpr .r6 + BitVec.ofNat 64 r30Off) (by decide) (by decide)
    (by rw [u₂.gpr, u₁.other _ (by decide)]) (by rw [u₂.wr, u₁.wr]; exact scr_in hW (by decide)) fun s₃ u₃ => ?_
  refine wp_std (a := s.gpr .r6 + BitVec.ofNat 64 r31Off) (by decide) (by decide)
    (by rw [u₃.gpr, u₂.gpr, u₁.other _ (by decide)]) (by rw [u₃.wr, u₂.wr, u₁.wr]; exact scr_in hW (by decide))
    fun s₄ u₄ => ?_
  refine wp_mr fun s₅ u₅ => wp_mr fun s₆ u₆ => wp_mr fun s₇ u₇ => wp_mr fun s₈ u₈ => wp_mr fun s₉ u₉ => ?_
  obtain g₄ : ∀ r, r ≠ .r0 → s₄.gpr r = s.gpr r := fun r h => by rw [u₄.gpr, u₃.gpr, u₂.gpr, u₁.other r h]
  refine k s₉ ⟨?_, ?_, ?_, ?_, ?_, fun r h0 h3 h4 h5 h30 h31 => ?_, ?_, ?_, ?_⟩
  · rw [u₉.other _ (by decide), u₈.other _ (by decide), u₇.gpr, u₆.other _ (by decide), u₅.other _ (by decide),
      g₄ _ (by decide)]
  · rw [u₉.other _ (by decide), u₈.gpr, u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide),
      g₄ _ (by decide)]
  · rw [u₉.gpr, u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide), u₅.gpr, g₄ _ (by decide)]
  · rw [u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide), u₆.gpr, u₅.other _ (by decide),
      g₄ _ (by decide)]
  · rw [u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide), u₅.gpr,
      g₄ _ (by decide)]
  · rw [u₉.other r h5, u₈.other r h4, u₇.other r h3, u₆.other r h30, u₅.other r h31, g₄ r h0]
  · rw [u₉.rd, u₈.rd, u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd]
  · rw [u₉.wr, u₈.wr, u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]
  · rw [u₉.mem, u₈.mem, u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem, u₃.gpr, u₂.gpr, u₁.gpr,
      u₁.other _ (by decide), u₁.other _ (by decide)]

theorem initZero_wp {t : State} {S B : Addr} (h31 : t.gpr .r31 = S) (h30 : t.gpr .r30 = B)
    (hW : (⟨B, 640⟩ : Region) ∈ t.wr) {Q : State → Prop}
    (k : ∀ u, u.gpr .r3 = S → u.gpr .r4 = B + BitVec.ofNat 64 512 → u.gpr .r5 = B →
      (∀ r, r ≠ .r0 → r ≠ .r3 → r ≠ .r4 → r ≠ .r5 → u.gpr r = t.gpr r) →
      u.mem = t.mem.writeW (B + BitVec.ofNat 64 512) (0 : BitVec 64) → u.rd = t.rd → u.wr = t.wr → Q u) :
    WP isa (.block initZero) t Q := by
  simp only [initZero, mr]
  refine wp_mr fun s₁ u₁ => wp_mr fun s₂ u₂ => wp_addi (by decide) (by decide) fun s₃ u₃ =>
    wp_li (by decide) fun s₄ u₄ => ?_
  refine wp_std (a := B + BitVec.ofNat 64 512) (by decide) (by decide)
    (by rw [u₄.other _ (by decide), u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide), h30, bufOff]; exact BitVec.add_zero _)
    (by rw [u₄.wr, u₃.wr, u₂.wr, u₁.wr]; exact scr_in hW (by decide)) fun s₅ u₅ => wp_nil ?_
  refine k s₅ ?_ ?_ ?_ (fun r h0 h3 h4 h5 => ?_) ?_ (by rw [u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd])
    (by rw [u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr])
  · rw [u₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr, h31]
  · rw [u₅.gpr, u₄.other _ (by decide), u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide), h30, bufOff]
  · rw [u₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr, u₁.other _ (by decide), h30]
  · rw [u₅.gpr, u₄.other r h0, u₃.other r h4, u₂.other r h5, u₁.other r h3]
  · rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem, u₄.gpr]
    rfl

/-- The subkeys from `L = rev64 [r4]`, the chaining value zeroed, and the
return address and the caller's `r30`, `r31` restored. -/
theorem initTail_wp {u : State} {S B : Addr} (h3 : u.gpr .r3 = S) (h4 : u.gpr .r4 = B + BitVec.ofNat 64 512)
    (h30 : u.gpr .r30 = B) (hS : (⟨S, 416⟩ : Region) ∈ u.wr) (hW : (⟨B, 640⟩ : Region) ∈ u.wr)
    (hd : Region.Disjoint ⟨S, 416⟩ ⟨B, 640⟩) {Q : State → Prop}
    (k : ∀ f, let L := rev64 (u.mem.readW (B + BitVec.ofNat 64 512) 64)
      f.mem = ((u.mem.writeW (S + BitVec.ofNat 64 384) (rev64 (dbl64 L))).writeW
        (S + BitVec.ofNat 64 384 + BitVec.ofNat 64 8) (rev64 (dbl64 (dbl64 L)))).writeW
        (S + BitVec.ofNat 64 400) (0 : BitVec 64) →
      f.gpr .r30 = u.mem.readW (B + BitVec.ofNat 64 r30Off) 64 →
      f.gpr .r31 = u.mem.readW (B + BitVec.ofNat 64 r31Off) 64 →
      f.lr = u.mem.readW (B + BitVec.ofNat 64 lrOff) 64 →
      (∀ r ∈ preserved, r ≠ .r30 → r ≠ .r31 → f.gpr r = u.gpr r) → Q f) :
    WP isa (.block (initSubkeys ++ initRestore)) u Q := by
  obtain inS : ∀ off, off + 8 ≤ 416 → InRegions u.wr (S + BitVec.ofNat 64 off) 8 := fun off h =>
    ⟨_, hS, VG.Offset.contains_base _ h (by omega_using [h])⟩
  -- The slots of the working space are apart from the state's.
  obtain sep : ∀ off, off + 8 ≤ 640 → ∀ off', off' + 8 ≤ 416 →
      Region.Disjoint ⟨B + BitVec.ofNat 64 off, 8⟩ ⟨S + BitVec.ofNat 64 off', 8⟩ := fun off h off' h' =>
    (hd.sub_left (VG.Offset.sub_base _ h')).symm.sub_left (VG.Offset.sub_base _ h)
  simp only [initSubkeys, initRestore, List.append_assoc, List.cons_append, List.nil_append]
  refine wp_li (by decide) fun s₁ u₁ => ?_
  refine wp_ldbrx (ea := B + BitVec.ofNat 64 512) (by decide)
    (by rw [u₁.gpr, u₁.other _ (by decide), h4, BitVec.add_zero]) (by rw [u₁.rd, u₁.wr]; exact scr_rd hW (by decide))
    fun s₂ u₂ => ?_
  refine dblCode_wp (by rw [u₂.other _ (by decide), u₁.gpr]; rfl) fun s₃ g₃ o₃ m₃ rd₃ wr₃ => ?_
  refine wp_li (by decide) fun s₄ u₄ => ?_
  refine wp_stdbrx (ea := S + BitVec.ofNat 64 384) (by decide)
    (by rw [u₄.gpr, u₄.other _ (by decide), o₃ _ (by decide) (by decide) (by decide) (by decide),
      u₂.other _ (by decide), u₁.other _ (by decide), h3])
    (by rw [u₄.wr, wr₃, u₂.wr, u₁.wr]; exact inS 384 (by decide)) fun s₅ u₅ => ?_
  refine dblCode_wp (by rw [u₅.gpr, u₄.other _ (by decide), o₃ _ (by decide) (by decide) (by decide) (by decide),
      u₂.other _ (by decide), u₁.gpr]; rfl) fun s₆ g₆ o₆ m₆ rd₆ wr₆ => ?_
  refine wp_li (by decide) fun s₇ u₇ => ?_
  refine wp_stdbrx (ea := S + BitVec.ofNat 64 384 + BitVec.ofNat 64 8) (by decide)
    (by rw [u₇.gpr, u₇.other _ (by decide), o₆ _ (by decide) (by decide) (by decide) (by decide), u₅.gpr,
      u₄.other _ (by decide), o₃ _ (by decide) (by decide) (by decide) (by decide),
      u₂.other _ (by decide), u₁.other _ (by decide), h3, VG.Offset.add_add])
    (by rw [u₇.wr, wr₆, u₅.wr, u₄.wr, wr₃, u₂.wr, u₁.wr, VG.Offset.add_add]; exact inS 392 (by decide))
    fun s₈ u₈ => ?_
  refine wp_li (by decide) fun s₉ u₉ => ?_
  obtain r3₉ : s₉.gpr .r3 = S := by
    rw [u₉.other _ (by decide), u₈.gpr, u₇.other _ (by decide), o₆ _ (by decide) (by decide) (by decide) (by decide),
      u₅.gpr, u₄.other _ (by decide), o₃ _ (by decide) (by decide) (by decide) (by decide), u₂.other _ (by decide),
      u₁.other _ (by decide), h3]
  obtain r30₉ : s₉.gpr .r30 = B := by
    rw [u₉.other _ (by decide), u₈.gpr, u₇.other _ (by decide), o₆ _ (by decide) (by decide) (by decide) (by decide),
      u₅.gpr, u₄.other _ (by decide), o₃ _ (by decide) (by decide) (by decide) (by decide), u₂.other _ (by decide),
      u₁.other _ (by decide), h30]
  obtain wr₉ : s₉.wr = u.wr := by rw [u₉.wr, u₈.wr, u₇.wr, wr₆, u₅.wr, u₄.wr, wr₃, u₂.wr, u₁.wr]
  obtain rd₉ : s₉.rd = u.rd := by rw [u₉.rd, u₈.rd, u₇.rd, rd₆, u₅.rd, u₄.rd, rd₃, u₂.rd, u₁.rd]
  refine wp_std (a := S + BitVec.ofNat 64 400) (by decide) (by decide) (by rw [r3₉])
    (by rw [wr₉]; exact inS 400 (by decide)) fun s₁₀ u₁₀ => ?_
  obtain hR : ∀ off, off + 8 ≤ 640 → InRegions (s₁₀.rd ++ s₁₀.wr) (B + BitVec.ofNat 64 off) 8 := fun off h => by
    rw [u₁₀.rd, u₁₀.wr, rd₉, wr₉]; exact scr_rd hW h
  refine wp_ld (a := B + BitVec.ofNat 64 lrOff) (by decide) (by decide) (by rw [u₁₀.gpr, r30₉])
    (hR lrOff (by decide)) fun s₁₁ u₁₁ => ?_
  refine wp_ld (a := B + BitVec.ofNat 64 r31Off) (by decide) (by decide)
    (by rw [u₁₁.other _ (by decide), u₁₀.gpr, r30₉]) (by rw [u₁₁.rd, u₁₁.wr]; exact hR r31Off (by decide))
    fun s₁₂ u₁₂ => ?_
  refine wp_ld (a := B + BitVec.ofNat 64 r30Off) (by decide) (by decide)
    (by rw [u₁₂.other _ (by decide), u₁₁.other _ (by decide), u₁₀.gpr, r30₉])
    (by rw [u₁₂.rd, u₁₂.wr, u₁₁.rd, u₁₁.wr]; exact hR r30Off (by decide)) fun s₁₃ u₁₃ => wp_mtlr (wp_nil ?_)
  -- The memory.
  obtain v₄ : s₄.gpr .r7 = dbl64 (rev64 (u.mem.readW (B + BitVec.ofNat 64 512) 64)) := by
    rw [u₄.other _ (by decide), g₃, u₂.gpr, u₁.mem]
  obtain v₇ : s₇.gpr .r7 = dbl64 (dbl64 (rev64 (u.mem.readW (B + BitVec.ofNat 64 512) 64))) := by
    rw [u₇.other _ (by decide), g₆, u₅.gpr, v₄]
  obtain m₁₀ : s₁₀.mem = ((u.mem.writeW (S + BitVec.ofNat 64 384)
      (rev64 (dbl64 (rev64 (u.mem.readW (B + BitVec.ofNat 64 512) 64))))).writeW
      (S + BitVec.ofNat 64 384 + BitVec.ofNat 64 8)
      (rev64 (dbl64 (dbl64 (rev64 (u.mem.readW (B + BitVec.ofNat 64 512) 64)))))).writeW
      (S + BitVec.ofNat 64 400) (0 : BitVec 64) := by
    rw [u₁₀.mem, u₉.gpr, u₉.mem, u₈.mem, u₇.mem, m₆, u₅.mem, u₄.mem, m₃, u₂.mem, u₁.mem, ← v₇, ← v₄]
    rfl
  obtain rdB : ∀ off, off + 8 ≤ 640 → s₁₀.mem.readW (B + BitVec.ofNat 64 off) 64 =
      u.mem.readW (B + BitVec.ofNat 64 off) 64 := fun off h => by
    rw [m₁₀, readW_sep64 (sep off h 400 (by decide)),
      readW_sep64 (by rw [VG.Offset.add_add]; exact sep off h 392 (by decide)), readW_sep64 (sep off h 384 (by decide))]
  refine k _ (by show s₁₃.mem = _; rw [u₁₃.mem, u₁₂.mem, u₁₁.mem, m₁₀]) ?_ ?_ ?_ (fun r hr h30' h31' => ?_)
  · show s₁₃.gpr .r30 = _; rw [u₁₃.gpr, u₁₂.mem, u₁₁.mem, rdB r30Off (by decide)]
  · show s₁₃.gpr .r31 = _; rw [u₁₃.other _ (by decide), u₁₂.gpr, u₁₁.mem, rdB r31Off (by decide)]
  · show s₁₃.gpr .r0 = _; rw [u₁₃.other _ (by decide), u₁₂.other _ (by decide), u₁₁.gpr, rdB lrOff (by decide)]
  · obtain ⟨h0, -, -, -, h6, h7, h8, h9, h10, h11, -⟩ := preserved_ne r hr
    show s₁₃.gpr r = _
    rw [u₁₃.other r h30', u₁₂.other r h31', u₁₁.other r h0, u₁₀.gpr, u₉.other r h0, u₈.gpr, u₇.other r h11,
      o₆ r h7 h8 h9 h10, u₅.gpr, u₄.other r h11, o₃ r h7 h8 h9 h10, u₂.other r h7, u₁.other r h6]

/-- The state after `stream_init`: the schedule, the subkeys and the chaining
value of the empty message. -/
theorem repr_init {m : Mem} {S : Addr} {key : List Byte} (hv : Spec.TripleDes.validKey key.length)
    (hs : Spec.TripleDes.scheduleAt m S = Spec.TripleDes.expandKey key)
    (hk : Spec.Aes.bytesAt m (S + 384) 16 =
      le8 (rev64 (dbl64 (Proof.CmacTripleDes.tdes (Spec.TripleDes.expandKey key) 0))) ++
        le8 (rev64 (dbl64 (dbl64 (Proof.CmacTripleDes.tdes (Spec.TripleDes.expandKey key) 0)))))
    (hc : Spec.Aes.bytesAt m (S + 400) 8 = le8 0) : Spec.Cmac.tdesRepr m S key [] := by
  refine ⟨hv, hs, ?_, ?_, ?_⟩
  · rw [hk, Spec.Cmac.tdes, Proof.CmacTripleDes.subkeys_tdes]; rfl
  · rw [hc, Proof.Cmac.le8_zero]; rfl
  · rfl

theorem init_wp (s : State) (hp : InitPre s) :
    WP isa streamInit s fun s' => (∀ r ∈ preserved, s'.gpr r = s.gpr r) ∧ s'.lr = s.lr ∧
      Spec.Cmac.tdesRepr s'.mem (s.gpr .r3) (Spec.TripleDes.bytesAt s.mem (s.gpr .r4) (s.gpr .r5).toNat) [] := by
  obtain hS : (⟨s.gpr .r3, 416⟩ : Region) ∈ s.wr := by rw [hp.wr]; simp
  obtain hW : (⟨s.gpr .r6, 640⟩ : Region) ∈ s.wr := by rw [hp.wr]; simp
  have hfitB := hp.scrFit
  have hfitS := hp.stateFit
  -- The working space's slots are apart from the schedule and the key.
  obtain slotSched : ∀ off, off + 8 ≤ 640 → Region.Disjoint ⟨s.gpr .r6 + BitVec.ofNat 64 off, 8⟩ ⟨s.gpr .r3, 384⟩ :=
    fun off h => (hp.stateScr.sub_left (Region.sub_prefix (by decide))).symm.sub_left (VG.Offset.sub_base _ h)
  unfold streamInit
  refine WP.seq ?_
  rw [← List.append_nil initSave]
  refine initSave_wp hp fun t ht => wp_nil ?_
  obtain keyIn : (⟨s.gpr .r4, (s.gpr .r5).toNat⟩ : Region) ∈ t.rd := by rw [ht.rd, hp.rd]; simp
  refine WP.seq (keyCall_wp (K := s.gpr .r4) (S := s.gpr .r3) (len := (s.gpr .r5).toNat) ht.r3
    (by rw [ht.r4, BitVec.ofNat_toNat, BitVec.setWidth_eq]) ht.r5 (s.gpr .r5).isLt keyIn (by rw [ht.wr]; exact hS)
    hp.keyState hp.valid fun t₁ rd₁ wr₁ f₁ c₁ sch₁ => ?_)
  obtain r31₁ : t₁.gpr .r31 = s.gpr .r3 := by rw [c₁ _ (by decide), ht.r31]
  obtain r30₁ : t₁.gpr .r30 = s.gpr .r6 := by rw [c₁ _ (by decide), ht.r30]
  refine WP.seq (initZero_wp r31₁ r30₁ (by rw [wr₁, ht.wr]; exact hW) fun u h3 h4 h5 hu mu rdu wru => ?_)
  obtain wru' : u.wr = s.wr := by rw [wru, wr₁, ht.wr]
  obtain rdu' : u.rd = s.rd := by rw [rdu, rd₁, ht.rd]
  refine WP.seq (encCall_wp h3 h4 h5 ⟨_, List.mem_append_right _ (by rw [wru']; exact hS),
      VG.Offset.contains_base _ (show 0 + 384 ≤ 416 by decide) (by decide) |> fun h => by simpa using h⟩
    (by rw [wru']; exact hW) (Nat.le_refl _) (hp.stateScr.sub_left (Region.sub_prefix (by decide)))
    fun v rdv wrv cv v3 v4 v5 fv outv => ?_)
  obtain wrv' : v.wr = s.wr := by rw [wrv, wru']
  refine initTail_wp v3 v4 (by rw [cv _ (by decide), hu _ (by decide) (by decide) (by decide) (by decide), r30₁])
    (by rw [wrv']; exact hS) (by rw [wrv']; exact hW) hp.stateScr fun f mf r30f r31f lrf rf => ?_
  -- The working space's saved slots, through the calls and the writes.
  obtain slot : ∀ off, 520 ≤ off → off + 8 ≤ 640 → v.mem.readW (s.gpr .r6 + BitVec.ofNat 64 off) 64 =
      t.mem.readW (s.gpr .r6 + BitVec.ofNat 64 off) 64 := fun off h1 h2 => by
    rw [fv.readW (Region.contains_self _ _) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact VG.Offset.disjoint_base _ (by omega_using [h1]) (by omega_using [h2])) (by decide),
      mu, readW_sep64 (VG.Offset.disjoint _ (.inr (by omega_using [h1])) (by omega_using [h2]) (by omega_using [])),
      f₁.readW (Region.contains_self _ _) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact slotSched off h2) (by decide)]
  refine ⟨fun r hr => ?_, ?_, ?_⟩
  · by_cases e30 : r = .r30
    · subst e30
      rw [r30f, slot r30Off (by decide) (by decide), ht.mem,
        readW_sep64 (VG.Offset.disjoint _ (by decide) (by decide) (by decide)), Mem.readW_writeW_self64]
    by_cases e31 : r = .r31
    · subst e31
      rw [r31f, slot r31Off (by decide) (by decide), ht.mem, Mem.readW_writeW_self64]
    obtain ⟨h0, h3', h4', h5', -⟩ := preserved_ne r hr
    rw [rf r hr e30 e31, cv r hr, hu r h0 h3' h4' h5', c₁ r hr, ht.regs r h0 h3' h4' h5' e30 e31]
  · rw [lrf, slot lrOff (by decide) (by decide), ht.mem,
      readW_sep64 (VG.Offset.disjoint _ (by decide) (by decide) (by decide)),
      readW_sep64 (VG.Offset.disjoint _ (by decide) (by decide) (by decide)), Mem.readW_writeW_self64]
  · -- Frames of the memory through the steps.
    obtain cB : ∀ off, off + 8 ≤ 640 → (⟨s.gpr .r6, 640⟩ : Region).Contains (s.gpr .r6 + BitVec.ofNat 64 off) (64 / 8) :=
      fun off h => VG.Offset.contains_base _ h (by omega_using [h])
    obtain F0 : Frame [⟨s.gpr .r6, 640⟩] s.mem t.mem := by
      rw [ht.mem]
      exact (((Frame.refl _ _).writeW List.mem_cons_self _ (cB lrOff (by decide))).writeW List.mem_cons_self _
        (cB r30Off (by decide))).writeW List.mem_cons_self _ (cB r31Off (by decide))
    obtain F2 : Frame [⟨s.gpr .r6, 640⟩] t₁.mem u.mem := by
      rw [mu]; exact (Frame.refl _ _).writeW List.mem_cons_self _ (cB 512 (by decide))
    obtain F3 : Frame [⟨s.gpr .r6, 640⟩] u.mem v.mem :=
      fv.sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact ⟨_, List.mem_singleton_self _, Region.sub_prefix (by decide)⟩
    obtain cS : ∀ off, 384 ≤ off → off + 8 ≤ 408 →
        (⟨s.gpr .r3 + BitVec.ofNat 64 384, 24⟩ : Region).Contains (s.gpr .r3 + BitVec.ofNat 64 off) (64 / 8) :=
      fun off h1 h2 => VG.Offset.contains _ h1 (by omega_using [h2]) (by omega_using [])
    obtain F4 : Frame [⟨s.gpr .r3 + BitVec.ofNat 64 384, 24⟩] v.mem f.mem := by
      rw [mf, VG.Offset.add_add]
      exact (((Frame.refl _ _).writeW List.mem_cons_self _ (cS 384 (by decide) (by decide))).writeW
        List.mem_cons_self _ (cS 392 (by decide) (by decide))).writeW List.mem_cons_self _ (cS 400 (by decide) (by decide))
    obtain schedOut : ∀ r ∈ [(⟨s.gpr .r3 + BitVec.ofNat 64 384, 24⟩ : Region), ⟨s.gpr .r6, 640⟩],
        Region.Disjoint ⟨s.gpr .r3, 384⟩ r := fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact VG.Offset.base_disjoint _ (by decide) (by omega_using [])
      · exact hp.stateScr.sub_left (Region.sub_prefix (by decide))
    obtain Fu : Frame [⟨s.gpr .r3 + BitVec.ofNat 64 384, 24⟩, ⟨s.gpr .r6, 640⟩] t₁.mem u.mem := F2.mono (by simp)
    obtain Ff : Frame [⟨s.gpr .r3 + BitVec.ofNat 64 384, 24⟩, ⟨s.gpr .r6, 640⟩] t₁.mem f.mem :=
      (Fu.trans (F3.mono (by simp))).trans (F4.mono (by simp))
    obtain keyEq : Spec.TripleDes.bytesAt t.mem (s.gpr .r4) (s.gpr .r5).toNat =
        Spec.TripleDes.bytesAt s.mem (s.gpr .r4) (s.gpr .r5).toNat :=
      List.map_congr_left fun i hi => F0.bytes (R := ⟨s.gpr .r4, (s.gpr .r5).toNat⟩)
        (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hp.keyScr)
        (by have := (s.gpr .r5).isLt; show (s.gpr .r5).toNat ≤ 2 ^ 64; omega_using []) (List.mem_range.mp hi)
    rw [keyEq] at sch₁
    obtain schU : Spec.TripleDes.scheduleAt u.mem (s.gpr .r3) =
        Spec.TripleDes.expandKey (Spec.TripleDes.bytesAt s.mem (s.gpr .r4) (s.gpr .r5).toNat) := by
      rw [Proof.TripleDes.scheduleAt_eq_of_frame _ Fu schedOut, sch₁]
    -- `L`.
    obtain zero : Spec.Aes.bytesAt u.mem (s.gpr .r6 + BitVec.ofNat 64 512) 8 = Spec.Cmac.zeros 8 := by
      rw [← Proof.Cmac.le8_readW, mu, Mem.readW_writeW_self64, Proof.Cmac.le8_zero]
    rw [schU, zero_block _ _ zero] at outv
    obtain hL := l_eq outv
    refine repr_init (by simpa [Spec.TripleDes.bytesAt] using hp.valid)
      (by rw [Proof.TripleDes.scheduleAt_eq_of_frame _ Ff schedOut, sch₁]) ?_ ?_
    · have drop : ∀ m : Mem, Spec.Aes.bytesAt (m.writeW (s.gpr .r3 + BitVec.ofNat 64 400) (0 : BitVec 64))
          (s.gpr .r3 + BitVec.ofNat 64 384) 16 = Spec.Aes.bytesAt m (s.gpr .r3 + BitVec.ofNat 64 384) 16 :=
        fun m => List.map_congr_left fun i hi =>
          ((Frame.refl [(⟨s.gpr .r3 + BitVec.ofNat 64 400, 8⟩ : Region)] m).writeW List.mem_cons_self
            (0 : BitVec 64) (Region.contains_self _ _)).bytes (R := ⟨s.gpr .r3 + BitVec.ofNat 64 384, 16⟩)
            (fun r hr => by
              simp only [List.mem_singleton] at hr; subst hr
              exact VG.Offset.disjoint _ (.inl (by decide)) (by omega_using []) (by omega_using [])) (by show 16 ≤ 2 ^ 64; decide)
            (List.mem_range.mp hi)
      show Spec.Aes.bytesAt f.mem (s.gpr .r3 + BitVec.ofNat 64 384) 16 = _
      rw [mf, drop, Proof.Cmac.bytesAt_store2, hL]
    · show Spec.Aes.bytesAt f.mem (s.gpr .r3 + BitVec.ofNat 64 400) 8 = _
      rw [← Proof.Cmac.le8_readW, mf, Mem.readW_writeW_self64]

end VG.Proof.CmacTripleDes.Stream.PPC64LE

end

end

/-! ### `CmacTripleDes.Stream.PPC64LE.AbsorbCorrect`, which only this module used -/

section

/-! ### `CmacTripleDes.Stream.PPC64LE.ChainPath`, which only this module used -/

section

/-! ### `CmacTripleDes.Stream.PPC64LE.Absorb`, which only this module used -/

section

/-!
# Streaming TDEA-CMAC on PPC64LE: `absorb`

`absorb_wp`: `absorb` appends the data to the message the state represents.
With `h = held count` bytes held back, if the data fit after them
(`len ≤ 8 - h`, which `absorbFlag` tests), it copies them there
(`repr_fill`); otherwise it completes the block held back with the data's
first `8 - h` bytes, chains it and the data's whole blocks but its last 1 to
8 bytes through the block function's calls, and holds those back
(`repr_chain`).
-/

@[expose] public section

namespace VG.Proof.CmacTripleDes.Stream.PPC64LE

open VG VG.PPC64LE VG.Impl.CmacTripleDes.Stream.PPC64LE
open VG.Proof.Cmac (le8)
open VG.Proof.CmacTripleDes.Stream (held nblocks)

/-- `absorb`'s precondition, with the working space of 688 bytes at `r7`. -/
structure AbsorbPre (s : State) : Prop where
  rd : s.rd = [⟨s.gpr .r5, (s.gpr .r6).toNat⟩]
  wr : s.wr = [⟨s.gpr .r3, 416⟩, ⟨s.gpr .r7, 688⟩]
  dataState : Region.Disjoint ⟨s.gpr .r5, (s.gpr .r6).toNat⟩ ⟨s.gpr .r3, 416⟩
  dataScr : Region.Disjoint ⟨s.gpr .r5, (s.gpr .r6).toNat⟩ ⟨s.gpr .r7, 688⟩
  stateScr : Region.Disjoint ⟨s.gpr .r3, 416⟩ ⟨s.gpr .r7, 688⟩
  stateFit : (s.gpr .r3).toNat + 416 ≤ 2 ^ 64
  dataFit : (s.gpr .r5).toNat + (s.gpr .r6).toNat ≤ 2 ^ 64
  scrFit : (s.gpr .r7).toNat + 688 ≤ 2 ^ 64

/-- After `absorbSave`. -/
structure ASaved (s t : State) : Prop where
  r29 : t.gpr .r29 = s.gpr .r5
  r5 : t.gpr .r5 = s.gpr .r7
  regs : ∀ r, r ≠ .r0 → r ≠ .r5 → r ≠ .r29 → t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  mem : t.mem = (((s.mem.writeW (s.gpr .r7 + BitVec.ofNat 64 lrOff) s.lr).writeW
    (s.gpr .r7 + BitVec.ofNat 64 r29Off) (s.gpr .r29)).writeW (s.gpr .r7 + BitVec.ofNat 64 r30Off) (s.gpr .r30)).writeW
    (s.gpr .r7 + BitVec.ofNat 64 r31Off) (s.gpr .r31)

theorem absorbSave_wp {s : State} (hp : AbsorbPre s) {is : List Instr} {Q : State → Prop}
    (k : ∀ t, ASaved s t → WP isa (.block is) t Q) : WP isa (.block (absorbSave ++ is)) s Q := by
  obtain hW : (⟨s.gpr .r7, 688⟩ : Region) ∈ s.wr := by rw [hp.wr]; simp
  obtain sl : ∀ off, off + 8 ≤ 688 → InRegions s.wr (s.gpr .r7 + BitVec.ofNat 64 off) 8 := fun off h =>
    ⟨_, hW, VG.Offset.contains_base _ h (by omega_using [h])⟩
  simp only [absorbSave, mr, List.cons_append, List.nil_append]
  refine wp_mflr fun s₁ u₁ => ?_
  refine wp_std (a := s.gpr .r7 + BitVec.ofNat 64 lrOff) (by decide) (by decide) (by rw [u₁.other _ (by decide)])
    (by rw [u₁.wr]; exact sl _ (by decide)) fun s₂ u₂ => ?_
  refine wp_std (a := s.gpr .r7 + BitVec.ofNat 64 r29Off) (by decide) (by decide)
    (by rw [u₂.gpr, u₁.other _ (by decide)]) (by rw [u₂.wr, u₁.wr]; exact sl _ (by decide)) fun s₃ u₃ => ?_
  refine wp_std (a := s.gpr .r7 + BitVec.ofNat 64 r30Off) (by decide) (by decide)
    (by rw [u₃.gpr, u₂.gpr, u₁.other _ (by decide)]) (by rw [u₃.wr, u₂.wr, u₁.wr]; exact sl _ (by decide))
    fun s₄ u₄ => ?_
  refine wp_std (a := s.gpr .r7 + BitVec.ofNat 64 r31Off) (by decide) (by decide)
    (by rw [u₄.gpr, u₃.gpr, u₂.gpr, u₁.other _ (by decide)])
    (by rw [u₄.wr, u₃.wr, u₂.wr, u₁.wr]; exact sl _ (by decide)) fun s₅ u₅ => ?_
  refine wp_mr fun s₆ u₆ => wp_mr fun s₇ u₇ => ?_
  obtain g₅ : ∀ r, r ≠ .r0 → s₅.gpr r = s.gpr r := fun r h => by rw [u₅.gpr, u₄.gpr, u₃.gpr, u₂.gpr, u₁.other r h]
  refine k s₇ ⟨?_, ?_, fun r h0 h5 h29 => ?_, ?_, ?_, ?_⟩
  · rw [u₇.other _ (by decide), u₆.gpr, g₅ _ (by decide)]
  · rw [u₇.gpr, u₆.other _ (by decide), g₅ _ (by decide)]
  · rw [u₇.other r h5, u₆.other r h29, g₅ r h0]
  · rw [u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd]
  · rw [u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]
  · rw [u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem, u₄.gpr, u₃.gpr, u₂.gpr, u₁.gpr,
      u₁.other .r29 (by decide), u₁.other .r30 (by decide), u₁.other .r31 (by decide)]

/-- `absorbFlag`'s flag: nonzero iff the data do not fit after the bytes
held back. -/
theorem flag_eq {h len : Nat} (hh : h ≤ 8) (hl : len < 2 ^ 64) :
    ((BitVec.ofNat 64 len >>> 4 ||| (BitVec.ofNat 64 (8 - h) - BitVec.ofNat 64 len) >>> 63) != 0) =
      decide (8 - h < len) := by
  have t0 : (0 : BitVec 64).toNat = 0 := rfl
  by_cases h16 : 16 ≤ len
  · have ha : (BitVec.ofNat 64 len >>> 4).toNat ≠ 0 := by
      rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hl, Nat.shiftRight_eq_div_pow]
      omega
    rw [decide_eq_true (by omega)]
    simp only [bne_iff_ne, ne_eq]
    intro e
    apply ha
    have := congrArg BitVec.toNat e
    rw [BitVec.toNat_or, t0, Nat.or_eq_zero_iff] at this
    exact this.1
  · have lo : BitVec.ofNat 64 len >>> 4 = 0 := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hl, Nat.shiftRight_eq_div_pow]
      simp; omega
    obtain z : ∀ y : BitVec 64, BitVec.ofNat 64 len >>> 4 ||| y = y := fun y => by rw [lo]; ext; simp
    rw [z]
    by_cases hc : 8 - h < len
    · rw [decide_eq_true hc]
      simp only [bne_iff_ne, ne_eq]
      intro e
      have := congrArg BitVec.toNat e
      rw [BitVec.toNat_ushiftRight, BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
        Nat.shiftRight_eq_div_pow] at this
      simp at this
      omega
    · rw [decide_eq_false hc]
      simp only [bne_eq_false_iff_eq]
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_ushiftRight, BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
        Nat.shiftRight_eq_div_pow]
      simp
      omega

/-- `absorbFlag`, after `heldCode`: the room left to `r9`, and the flag to
`r10`. -/
theorem flag_wp {t : State} {h len : Nat} (hh : h ≤ 8) (hl : len < 2 ^ 64)
    (h8 : t.gpr .r8 = BitVec.ofNat 64 h) (h6 : t.gpr .r6 = BitVec.ofNat 64 len) {is : List Instr} {Q : State → Prop}
    (k : ∀ u, u.gpr .r9 = BitVec.ofNat 64 (8 - h) →
      isa.eval (.nonzero .d .r10) u = some (decide (8 - h < len)) →
      (∀ r, r ≠ .r9 → r ≠ .r10 → r ≠ .r11 → u.gpr r = t.gpr r) → u.mem = t.mem → u.rd = t.rd → u.wr = t.wr →
      WP isa (.block is) u Q) :
    WP isa (.block (absorbFlag ++ is)) t Q := by
  simp only [absorbFlag, List.cons_append, List.nil_append]
  refine wp_li (by decide) fun t₁ u₁ => wp_sub fun t₂ u₂ => wp_lsr (by decide) fun t₃ u₃ =>
    wp_sub fun t₄ u₄ => wp_lsr (by decide) fun t₅ u₅ => wp_or fun t₆ u₆ => ?_
  obtain r9 : t₂.gpr .r9 = BitVec.ofNat 64 (8 - h) := by
    rw [u₂.gpr, u₁.gpr, u₁.other _ (by decide), h8, VG.Offset.ofNat_sub_ofNat hh]
  obtain r6 : t₃.gpr .r6 = BitVec.ofNat 64 len := by
    rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), h6]
  refine k t₆ (by rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), r9])
    ?_ (fun r h9 h10 h11 => by
      rw [u₆.other r h10, u₅.other r h11, u₄.other r h11, u₃.other r h10, u₂.other r h9, u₁.other r h9])
    (by rw [u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]) (by rw [u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd])
    (by rw [u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr])
  rw [eval_nonzero, u₆.gpr, u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, u₂.other _ (by decide),
    u₁.other _ (by decide), h6, u₅.gpr, u₄.gpr, u₃.other _ (by decide), r9, r6, flag_eq hh hl]

theorem WP.seq_seq {A B C : Prog isa} {s : State} {Q : State → Prop}
    (h : WP isa (.seq A B) s fun t => WP isa C t Q) : WP isa (.seq A (.seq B C)) s Q := by
  rw [WP.seq_iff] at h ⊢; exact WP.mono h fun _ ht => WP.seq_iff.mpr ht

/-- What the two paths (`chainPath`, `fillPath`) start from: `count`'s
bytes held back `h` in `r8`, the room left in `r9`, the data (`D`, `len`)
in `r29` and `r6`, and the working space at `W` in `r5`. -/
structure PathEnv (u : State) (S D W : Addr) (len h : Nat) : Prop where
  r3 : u.gpr .r3 = S
  r5 : u.gpr .r5 = W
  r6 : u.gpr .r6 = BitVec.ofNat 64 len
  r8 : u.gpr .r8 = BitVec.ofNat 64 h
  r9 : u.gpr .r9 = BitVec.ofNat 64 (8 - h)
  r29 : u.gpr .r29 = D
  hh : h ≤ 8
  lenLt : len < 2 ^ 64
  data : (⟨D, len⟩ : Region) ∈ u.rd
  state : (⟨S, 416⟩ : Region) ∈ u.wr
  scr : (⟨W, 688⟩ : Region) ∈ u.wr
  dataState : Region.Disjoint ⟨D, len⟩ ⟨S, 416⟩
  dataScr : Region.Disjoint ⟨D, len⟩ ⟨W, 688⟩
  stateScr : Region.Disjoint ⟨S, 416⟩ ⟨W, 688⟩
  stateFit : S.toNat + 416 ≤ 2 ^ 64
  dataFit : D.toNat + len ≤ 2 ^ 64
  scrFit : W.toNat + 688 ≤ 2 ^ 64

/-- What both paths keep. -/
structure PathOut (u : State) (S W : Addr) (v : State) : Prop where
  regs : ∀ r ∈ preserved, r ≠ .r29 → r ≠ .r30 → r ≠ .r31 → v.gpr r = u.gpr r
  r5 : v.gpr .r5 = W
  rd : v.rd = u.rd
  wr : v.wr = u.wr
  frame : Frame [⟨S, 416⟩, ⟨W, 520⟩] u.mem v.mem

/-- A copy of `n` bytes from `src` to `dst`. -/
structure Copied (m : Mem) (src dst : Addr) (n : Nat) (m' : Mem) : Prop where
  copied : ∀ i < n, m' (dst + BitVec.ofNat 64 i) = m (src + BitVec.ofNat 64 i)
  rest : ∀ x, (∀ i < n, x ≠ dst + BitVec.ofNat 64 i) → m' x = m x

/-- The bytes `[a, a + n)` of the state are apart from those of the data. -/
theorem state_ne_data {S D : Addr} {len : Nat} (hd : Region.Disjoint ⟨D, len⟩ ⟨S, 416⟩)
    (hD : D.toNat + len ≤ 2 ^ 64) {i j : Nat} (hi : i < len) (hj : j < 416) :
    D + BitVec.ofNat 64 i ≠ S + BitVec.ofNat 64 j := fun e =>
  hd _ (VG.Offset.contains_base _ (show i + 1 ≤ len by omega_using [hi]) (by omega_using [hD, hi]))
    (by rw [e]; exact VG.Offset.contains_base _ (show j + 1 ≤ 416 by omega_using [hj]) (by omega_using [hj]))

/-- `toHeld n` and the copy: `count` bytes of the data at `r29` after the
`h` bytes held back. -/
theorem toHeld_copy_wp {u : State} {S D W : Addr} {len h : Nat} (he : PathEnv u S D W len h) {n : Reg}
    (hn10 : n ≠ .r10) (hn11 : n ≠ .r11) {cnt : Nat} (hc : u.gpr n = BitVec.ofNat 64 cnt) (hcl : cnt ≤ len)
    (hch : h + cnt ≤ 8) {Q : State → Prop}
    (k : ∀ v, v.gpr .r10 = D + BitVec.ofNat 64 cnt →
      (∀ r, r ≠ .r0 → r ≠ .r10 → r ≠ .r11 → r ≠ .r12 → v.gpr r = u.gpr r) → v.rd = u.rd → v.wr = u.wr →
      Copied u.mem D (S + BitVec.ofNat 64 (408 + h)) cnt v.mem → Q v) :
    WP isa (.seq (.block (toHeld n)) copyLoop) u Q := by
  have hh := he.hh
  have hS := he.stateFit
  have hD := he.dataFit
  refine WP.seq ?_
  simp only [toHeld, mr]
  refine wp_addi (by decide) (by decide) fun t₁ u₁ => wp_add fun t₂ u₂ => wp_mr fun t₃ u₃ => wp_mr fun t₄ u₄ =>
    wp_nil ?_
  obtain g₄ : ∀ r, r ≠ .r10 → r ≠ .r11 → r ≠ .r12 → t₄.gpr r = u.gpr r := fun r h10 h11 h12 => by
    rw [u₄.other r h12, u₃.other r h10, u₂.other r h11, u₁.other r h11]
  obtain rd₄ : t₄.rd = u.rd := by rw [u₄.rd, u₃.rd, u₂.rd, u₁.rd]
  obtain wr₄ : t₄.wr = u.wr := by rw [u₄.wr, u₃.wr, u₂.wr, u₁.wr]
  obtain m₄ : t₄.mem = u.mem := by rw [u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  refine copyLoop_wp (src := D) (dst := S + BitVec.ofNat 64 (408 + h)) (n := cnt) (by omega_using [hch])
    (by rw [u₄.other _ (by decide), u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide), he.r29])
    (by rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr, u₁.gpr, u₁.other _ (by decide), he.r3, he.r8,
      VG.Offset.add_add])
    (by rw [u₄.gpr, u₃.other _ hn10, u₂.other _ hn11, u₁.other _ hn11, hc])
    (fun i hi => by
      rw [rd₄, wr₄]
      exact ⟨_, List.mem_append_left _ he.data, VG.Offset.contains_base _ (show i + 1 ≤ len by omega_using [hcl, hi]) (by omega_using [hch, hi])⟩)
    (fun i hi => by
      rw [wr₄, VG.Offset.add_add]
      exact ⟨_, he.state, VG.Offset.contains_base _ (show 408 + h + i + 1 ≤ 416 by omega_using [hch, hi]) (by omega_using [hch, hi])⟩)
    (fun i hi i' hi' => by
      rw [VG.Offset.add_add]; exact state_ne_data he.dataState hD (by omega_using [hcl, hi]) (by omega_using [hch, hi']))
    fun v hv => ?_
  exact k v hv.r10 (fun r h0 h10 h11 h12 => by rw [hv.regs r h0 h10 h11 h12, g₄ r h10 h11 h12])
    (by rw [hv.rd, rd₄]) (by rw [hv.wr, wr₄])
    ⟨fun i hi => by rw [hv.copied i hi, m₄], fun x hx => by rw [hv.rest x hx, m₄]⟩

/-- A copy into the state keeps the rest of memory. -/
theorem Copied.frame {m m' : Mem} {src S W : Addr} {a n : Nat} (hc : Copied m src (S + BitVec.ofNat 64 a) n m')
    (ha : a + n ≤ 416) : Frame [⟨S, 416⟩, ⟨W, 520⟩] m m' := fun x hx =>
  hc.rest x fun i hi e => hx _ List.mem_cons_self (by
    rw [e, VG.Offset.add_add]; exact VG.Offset.contains_base _ (show a + i + 1 ≤ 416 by omega_using [ha, hi]) (by omega_using [ha, hi]))

theorem fill_wp {u : State} {S D W : Addr} {len h : Nat} (he : PathEnv u S D W len h) (hf : len ≤ 8 - h) :
    WP isa fillPath u fun v => PathOut u S W v ∧ Copied u.mem D (S + BitVec.ofNat 64 (408 + h)) len v.mem := by
  have hh := he.hh
  exact toHeld_copy_wp he (by decide) (by decide) he.r6 (Nat.le_refl _) (by omega_using [hf, hh])
    fun v _ hv rd wr hc => ⟨⟨fun r hr _ _ _ => by
      obtain ⟨h0, -, -, -, -, -, -, -, h10, h11, h12⟩ := preserved_ne r hr
      exact hv r h0 h10 h11 h12, by rw [hv _ (by decide) (by decide) (by decide) (by decide), he.r5], rd, wr,
      hc.frame (by omega_using [hf, hh])⟩, hc⟩

end VG.Proof.CmacTripleDes.Stream.PPC64LE

end

end

/-! ### `CmacTripleDes.Stream.PPC64LE.Chain`, which only this module used -/

section

/-!
# Streaming TDEA-CMAC on PPC64LE: `absorb`'s chaining loop

`chainLoop_wp`: each of the `nb` runs of `chainBody` XORs the next block of
the data at `P` into the buffer (`bufOff` in the working space at `W`) and
enciphers it, so that the buffer ends as the chain of those blocks from its
first value.
-/

@[expose] public section

namespace VG.Proof.CmacTripleDes.Stream.PPC64LE

open VG VG.PPC64LE VG.Impl.CmacTripleDes.Stream.PPC64LE
open VG.Proof.Cmac (le8)

/-- The block function's output, as bytes. -/
theorem enc_bytes {m m' : Mem} {a : Addr} {K : Spec.TripleDes.Schedule}
    (h : Spec.TripleDes.blockAt m' a = Spec.TripleDes.encryptBlock K (Spec.TripleDes.blockAt m a)) :
    Spec.Aes.bytesAt m' a 8 = Spec.Cmac.tdesWith K (Spec.Aes.bytesAt m a 8) := by
  rw [VG.Proof.TripleDes.bytesAt_eq, h, ← VG.Proof.TripleDes.ofFn_bytesAt]; rfl

theorem blocksAt_succ8 (m : Mem) (p : Addr) (j : Nat) :
    Spec.Cmac.blocksAt m p 8 (j + 1) =
      Spec.Cmac.blocksAt m p 8 j ++ [Spec.Aes.bytesAt m (p + BitVec.ofNat 64 (8 * j)) 8] := by
  simp [Spec.Cmac.blocksAt, List.range_succ]

/-- After `j` of the `nb` blocks, from the state `c` before the loop. -/
structure LoopInv (c : State) (S W P : Addr) (nb j : Nat) (t : State) : Prop where
  r3 : t.gpr .r3 = S
  r4 : t.gpr .r4 = W + BitVec.ofNat 64 512
  r5 : t.gpr .r5 = W
  r29 : t.gpr .r29 = P + BitVec.ofNat 64 (8 * j)
  r30 : t.gpr .r30 = BitVec.ofNat 64 (nb - j)
  regs : ∀ r ∈ preserved, r ≠ .r29 → r ≠ .r30 → t.gpr r = c.gpr r
  rd : t.rd = c.rd
  wr : t.wr = c.wr
  frame : Frame [⟨W, 520⟩] c.mem t.mem
  buf : Spec.Aes.bytesAt t.mem (W + BitVec.ofNat 64 512) 8 =
    Spec.Cmac.chain (Spec.Cmac.tdesWith (Spec.TripleDes.scheduleAt c.mem S))
      (Spec.Aes.bytesAt c.mem (W + BitVec.ofNat 64 512) 8) (Spec.Cmac.blocksAt c.mem P 8 j)

/-- What the loop needs of the state before it. -/
structure LoopEnv (c : State) (S W P : Addr) (nb : Nat) : Prop where
  key : InRegions (c.rd ++ c.wr) S 384
  scr : ∃ L, 640 ≤ L ∧ (⟨W, L⟩ : Region) ∈ c.wr
  keyScr : Region.Disjoint ⟨S, 384⟩ ⟨W, 640⟩
  scrFit : W.toNat + 640 ≤ 2 ^ 64
  data : ∀ j < nb, InRegions (c.rd ++ c.wr) (P + BitVec.ofNat 64 (8 * j)) 8
  dataScr : ∀ j < nb, Region.Disjoint ⟨P + BitVec.ofNat 64 (8 * j), 8⟩ ⟨W, 520⟩
  nbLt : nb < 2 ^ 64

theorem body_step {c t : State} {S W P : Addr} {nb j : Nat} (he : LoopEnv c S W P nb) (hj : j < nb)
    (hI : LoopInv c S W P nb j t) : WP isa chainBody t (LoopInv c S W P nb (j + 1)) := by
  obtain ⟨L, hL, hW⟩ := he.scr
  obtain hWt : (⟨W, L⟩ : Region) ∈ t.wr := by rw [hI.wr]; exact hW
  obtain bufIn : (⟨W, L⟩ : Region).Contains (W + BitVec.ofNat 64 512) 8 :=
    VG.Offset.contains_base _ (show 512 + 8 ≤ L by omega_using [hL]) (by omega_using [])
  obtain buf520 : (⟨W, 520⟩ : Region).Contains (W + BitVec.ofNat 64 512) (64 / 8) :=
    VG.Offset.contains_base _ (show 512 + 64 / 8 ≤ 520 by decide) (by omega_using [])
  unfold chainBody
  refine WP.seq ?_
  refine wp_ld (a := W + BitVec.ofNat 64 512) (by decide) (by decide) (by rw [hI.r5]; rfl)
    (by rw [hI.rd, hI.wr]; exact ⟨_, List.mem_append_right _ hW, bufIn⟩) fun t₁ u₁ => ?_
  refine wp_ld (a := P + BitVec.ofNat 64 (8 * j)) (by decide) (by decide)
    (by rw [u₁.other _ (by decide), hI.r29]; exact BitVec.add_zero _)
    (by rw [u₁.rd, u₁.wr, hI.rd, hI.wr]; exact he.data j hj) fun t₂ u₂ => wp_xor fun t₃ u₃ => ?_
  refine wp_std (a := W + BitVec.ofNat 64 512) (by decide) (by decide)
    (by rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), hI.r5]; rfl)
    (by rw [u₃.wr, u₂.wr, u₁.wr]; exact ⟨_, hWt, bufIn⟩) fun t₄ u₄ => ?_
  refine wp_addi (by decide) (by decide) fun t₅ u₅ => wp_subi (by decide) (by decide) fun t₆ u₆ =>
    wp_nil (Q := fun t₆ => WP isa encCall t₆ _) ?_
  obtain g₄ : ∀ r, r ≠ .r7 → r ≠ .r9 → t₄.gpr r = t.gpr r := fun r h7 h9 => by
    rw [u₄.gpr, u₃.other r h7, u₂.other r h9, u₁.other r h7]
  obtain g₆ : ∀ r, r ≠ .r7 → r ≠ .r9 → r ≠ .r29 → r ≠ .r30 → t₆.gpr r = t.gpr r := fun r h7 h9 h29 h30 => by
    rw [u₆.other r h30, u₅.other r h29, g₄ r h7 h9]
  obtain m₆ : t₆.mem = t.mem.writeW (W + BitVec.ofNat 64 512)
      (t.mem.readW (W + BitVec.ofNat 64 512) 64 ^^^ t.mem.readW (P + BitVec.ofNat 64 (8 * j)) 64) := by
    rw [u₆.mem, u₅.mem, u₄.mem, u₃.gpr, u₂.other _ (by decide), u₂.gpr, u₁.gpr, u₃.mem, u₂.mem, u₁.mem]
  obtain rd₆ : t₆.rd = c.rd := by rw [u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd, hI.rd]
  obtain wr₆ : t₆.wr = c.wr := by rw [u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr, hI.wr]
  obtain F₆ : Frame [⟨W, 520⟩] c.mem t₆.mem := by
    rw [m₆]; exact hI.frame.writeW List.mem_cons_self _ buf520
  -- The state's schedule and the data are outside what the loop writes.
  obtain hKW : ∀ r ∈ [(⟨W, 520⟩ : Region)], (⟨S, 384⟩ : Region).Disjoint r := fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact he.keyScr.sub_right (Region.sub_prefix (by decide))
  refine encCall_wp (S := S) (B := W) (L := L) (by rw [g₆ _ (by decide) (by decide) (by decide) (by decide), hI.r3])
    (by rw [g₆ _ (by decide) (by decide) (by decide) (by decide), hI.r4])
    (by rw [g₆ _ (by decide) (by decide) (by decide) (by decide), hI.r5])
    (by rw [rd₆, wr₆]; exact he.key) (by rw [wr₆]; exact hW) hL he.keyScr
    fun v rdv wrv cv v3 v4 v5 fv outv => ?_
  refine ⟨v3, v4, v5, ?_, ?_, fun r hr h29 h30 => ?_, by rw [rdv, rd₆], by rw [wrv, wr₆], F₆.trans fv, ?_⟩
  · rw [cv _ (by decide), u₆.other _ (by decide), u₅.gpr, u₄.gpr, u₃.other _ (by decide), u₂.other _ (by decide),
      u₁.other _ (by decide), hI.r29, VG.Offset.add_add, show 8 * j + 8 = 8 * (j + 1) by omega_using []]
  · rw [cv _ (by decide), u₆.gpr, u₅.other _ (by decide), u₄.gpr, u₃.other _ (by decide),
      u₂.other _ (by decide), u₁.other _ (by decide), hI.r30]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    have := he.nbLt
    omega_using [hj]
  · obtain ⟨-, -, -, -, -, h7, -, h9, -, -, -⟩ := preserved_ne r hr
    rw [cv r hr, g₆ r h7 h9 h29 h30, hI.regs r hr h29 h30]
  · have hdata : Spec.Aes.bytesAt t.mem (P + BitVec.ofNat 64 (8 * j)) 8 =
        Spec.Aes.bytesAt c.mem (P + BitVec.ofNat 64 (8 * j)) 8 :=
      List.map_congr_left fun i hi => hI.frame.bytes (R := ⟨P + BitVec.ofNat 64 (8 * j), 8⟩) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact he.dataScr j hj) (by show 8 ≤ 2 ^ 64; decide) (List.mem_range.mp hi)
    rw [enc_bytes outv, Proof.TripleDes.scheduleAt_eq_of_frame _ F₆ hKW, m₆, ← Proof.Cmac.le8_readW,
      Mem.readW_writeW_self64, Proof.Cmac.le8_xor, Proof.Cmac.le8_readW, Proof.Cmac.le8_readW, hI.buf, hdata,
      blocksAt_succ8, Proof.Cmac.chain_append, Proof.Cmac.chain_single]

theorem chainLoop_wp {c : State} {S W P : Addr} {nb : Nat} (he : LoopEnv c S W P nb)
    {Q : State → Prop} (h0 : LoopInv c S W P nb 0 c) (k : ∀ t, LoopInv c S W P nb nb t → Q t) :
    WP isa chainLoop c Q := by
  unfold chainLoop
  by_cases hz : nb = 0
  · subst hz
    exact WP.ite true (by rw [eval_zero_ofNat c .r30 (by decide) h0.r30]; rfl) (fun _ => wp_nil (k c h0))
      (fun h => by cases h)
  refine WP.ite false (by rw [eval_zero_ofNat c .r30 he.nbLt h0.r30]; simp [hz]) (fun h => by cases h)
    fun _ => ?_
  refine WP.loop (M := isa) (Q := Q)
    (fun (m : Nat) (t : State) => ∃ j, m = nb - j ∧ j < nb ∧ LoopInv c S W P nb j t) ?_ nb c
    ⟨0, by omega_using [], by omega_using [hz], h0⟩
  rintro _ t ⟨j, rfl, hj, hI⟩
  refine WP.mono (body_step he hj hI) fun t' h' => ?_
  obtain e := eval_nonzero_ofNat' t' .r30 (k := nb - (j + 1)) (by have := he.nbLt; omega_using [this]) h'.r30
  by_cases hf : j + 1 = nb
  · left; exact ⟨by rw [e]; simp [hf], k t' (hf ▸ h')⟩
  · right; exact ⟨by rw [e]; simp; omega_using [hj, hf], nb - (j + 1), by omega_using [hj], j + 1, rfl, by omega_using [hj, hf], h'⟩

end VG.Proof.CmacTripleDes.Stream.PPC64LE

end

end


/-!
# Streaming TDEA-CMAC on PPC64LE: `absorb`'s chaining path

`chain_wp`: when the data do not fit after the `h` bytes held back,
`chainPath` completes the block held back with the data's first `8 - h`
bytes, chains it (`chainSetup` and a call of the block function) and the
data's `nb` whole blocks after them (`chainLoop_wp`), writes the chaining
value back to the state (`chainDone`), and copies the data's last `rest`
bytes to the bytes held back.
-/

@[expose] public section

namespace VG.Proof.CmacTripleDes.Stream.PPC64LE

open VG VG.PPC64LE VG.Impl.CmacTripleDes.Stream.PPC64LE
open VG.Proof.Cmac (le8)

theorem shr3_ofNat {a : Nat} (ha : a < 2 ^ 64) : BitVec.ofNat 64 a >>> 3 = BitVec.ofNat 64 (a / 8) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha,
    Nat.shiftRight_eq_div_pow, Nat.mod_eq_of_lt (by omega_arith)]

theorem shl3_ofNat {n : Nat} (hn : 8 * n < 2 ^ 64) : BitVec.ofNat 64 n <<< 3 = BitVec.ofNat 64 (8 * n) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftLeft_eq, Nat.mod_eq_of_lt (by omega_arith),
    Nat.mod_eq_of_lt (by omega_arith), Nat.mod_eq_of_lt hn]
  omega_arith

/-- The whole blocks the path chains after the block held back. -/
abbrev nbOf (len f : Nat) : Nat := (len - f - 1) / 8

/-- The bytes it holds back after them. -/
abbrev restOf (len f : Nat) : Nat := len - f - 8 * nbOf len f

/-- What the path leaves in memory: the chaining value of the block held
back, completed by the data's first `f = 8 - h` bytes, and of the data's
`nb` whole blocks after them; the bytes after those held back. -/
structure ChainMem (m : Mem) (S D : Addr) (len h : Nat) (m' : Mem) : Prop where
  key : ∀ i < 400, m' (S + BitVec.ofNat 64 i) = m (S + BitVec.ofNat 64 i)
  chain : Spec.Aes.bytesAt m' (S + BitVec.ofNat 64 400) 8 =
    Spec.Cmac.chain (Spec.Cmac.tdesWith (Spec.TripleDes.scheduleAt m S)) (Spec.Aes.bytesAt m (S + BitVec.ofNat 64 400) 8)
      ([Spec.Aes.bytesAt m (S + BitVec.ofNat 64 408) h ++ Spec.Aes.bytesAt m D (8 - h)] ++
        Spec.Cmac.blocksAt m (D + BitVec.ofNat 64 (8 - h)) 8 (nbOf len (8 - h)))
  held : Spec.Aes.bytesAt m' (S + BitVec.ofNat 64 408) (restOf len (8 - h)) =
    Spec.Aes.bytesAt m (D + BitVec.ofNat 64 (8 - h + 8 * nbOf len (8 - h))) (restOf len (8 - h))

theorem chain_wp {u : State} {S D W : Addr} {len h : Nat} (he : PathEnv u S D W len h) (hc : 8 - h < len) :
    WP isa chainPath u fun v => PathOut u S W v ∧ ChainMem u.mem S D len h v.mem := by
  have hh := he.hh
  have hl := he.lenLt
  have hS := he.stateFit
  have hD := he.dataFit
  have hWf := he.scrFit
  generalize hf : 8 - h = f at hc ⊢
  obtain hnb8 : 8 * nbOf len f ≤ len - f - 1 := by show 8 * ((len - f - 1) / 8) ≤ _; omega_arith
  have hnbe : nbOf len f = (len - f - 1) / 8 := rfl
  obtain hrest : 1 ≤ restOf len f ∧ restOf len f ≤ 8 := by
    show 1 ≤ len - f - 8 * ((len - f - 1) / 8) ∧ len - f - 8 * ((len - f - 1) / 8) ≤ 8; omega_arith
  have hreste : restOf len f = len - f - 8 * nbOf len f := rfl
  generalize hnb : nbOf len f = nb at hnb8 hnbe hreste ⊢
  generalize hr : restOf len f = rest at hrest hreste ⊢
  -- Regions.
  have hWu : (⟨W, 688⟩ : Region) ∈ u.wr := he.scr
  obtain dataIn : ∀ a n, a + n ≤ len → InRegions (u.rd ++ u.wr) (D + BitVec.ofNat 64 a) n := fun a n h =>
    ⟨_, List.mem_append_left _ he.data, VG.Offset.contains_base _ h (by omega_arith)⟩
  obtain stIn : ∀ a n, a + n ≤ 416 → InRegions u.wr (S + BitVec.ofNat 64 a) n := fun a n h =>
    ⟨_, he.state, VG.Offset.contains_base _ h (by omega_arith)⟩
  obtain dataW : ∀ a n, a + n ≤ len → ∀ r ∈ [(⟨W, 520⟩ : Region)], Region.Disjoint ⟨D + BitVec.ofNat 64 a, n⟩ r :=
    fun a n h r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (he.dataScr.sub_right (Region.sub_prefix (by decide))).sub_left (VG.Offset.sub_base _ h)
  obtain dataS : ∀ a n, a + n ≤ len → Region.Disjoint ⟨D + BitVec.ofNat 64 a, n⟩ ⟨S + BitVec.ofNat 64 400, 16⟩ :=
    fun a n h => (he.dataState.sub_right (VG.Offset.sub_base _ (by decide))).sub_left (VG.Offset.sub_base _ h)
  obtain keyW : ∀ r ∈ [(⟨W, 520⟩ : Region)], (⟨S, 384⟩ : Region).Disjoint r := fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact (he.stateScr.sub_right (Region.sub_prefix (by decide))).sub_left (Region.sub_prefix (by decide))
  obtain keyS : ∀ r ∈ [(⟨S + BitVec.ofNat 64 400, 16⟩ : Region)], (⟨S, 384⟩ : Region).Disjoint r := fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact VG.Offset.base_disjoint _ (by decide) (by omega_arith)
  unfold chainPath
  -- The block held back, completed.
  refine WP.seq_seq (toHeld_copy_wp he (by decide) (by decide) (cnt := f) (by rw [he.r9, hf]) (by omega_arith) (by omega_arith)
    fun v₁ r10₁ g₁ rd₁ wr₁ cp₁ => ?_)
  obtain m₁S : Frame [⟨S + BitVec.ofNat 64 400, 16⟩] u.mem v₁.mem := fun x hx =>
    cp₁.rest x fun i hi e => hx _ List.mem_cons_self (by
      rw [e, VG.Offset.add_add]
      exact VG.Offset.contains _ (show 400 ≤ 408 + h + i by omega_arith) (show 408 + h + i + 1 ≤ 400 + 16 by omega_arith)
        (by omega_arith))
  obtain heldB : Spec.Aes.bytesAt v₁.mem (S + BitVec.ofNat 64 408) 8 =
      Spec.Aes.bytesAt u.mem (S + BitVec.ofNat 64 408) h ++ Spec.Aes.bytesAt u.mem D f := by
    rw [show 8 = h + f by omega_arith, Proof.Cmac.Stream.bytesAt_append, VG.Offset.add_add]
    congr 1
    · refine Proof.CmacTripleDes.Stream.bytesAt_congr fun i hi => ?_
      rw [VG.Offset.add_add]
      exact cp₁.rest _ fun i' hi' => by
        rw [VG.Offset.add_add]; exact VG.Offset.add_ofNat_ne _ (by omega_arith) (by omega_arith) (by omega_arith)
    · exact List.map_congr_left fun i hi => cp₁.copied i (List.mem_range.mp hi)
  obtain v3 : v₁.gpr .r3 = S := by rw [g₁ _ (by decide) (by decide) (by decide) (by decide), he.r3]
  obtain v5 : v₁.gpr .r5 = W := by rw [g₁ _ (by decide) (by decide) (by decide) (by decide), he.r5]
  obtain v6 : v₁.gpr .r6 = BitVec.ofNat 64 len := by rw [g₁ _ (by decide) (by decide) (by decide) (by decide), he.r6]
  obtain v9 : v₁.gpr .r9 = BitVec.ofNat 64 f := by
    rw [g₁ _ (by decide) (by decide) (by decide) (by decide), he.r9, hf]
  obtain stRd : ∀ (t : State), t.rd = u.rd → t.wr = u.wr → ∀ a n, a + n ≤ 416 →
      InRegions (t.rd ++ t.wr) (S + BitVec.ofNat 64 a) n := fun t hrd hwr a n h => by
    rw [hrd, hwr]; exact ⟨_, List.mem_append_right _ he.state, VG.Offset.contains_base _ h (by omega_arith)⟩
  obtain bufW : ∀ (t : State), t.wr = u.wr → InRegions t.wr (W + BitVec.ofNat 64 512) 8 := fun t hwr => by
    rw [hwr]; exact ⟨_, hWu, VG.Offset.contains_base _ (show 512 + 8 ≤ 688 by decide) (by omega_arith)⟩
  -- The counts, and the block held back XORed into the chaining value.
  refine WP.seq ?_
  simp only [chainSetup, mr]
  refine wp_mr fun w₁ x₁ => wp_sub fun w₂ x₂ => wp_subi (by decide) (by decide) fun w₃ x₃ =>
    wp_lsr (by decide) fun w₄ x₄ => wp_sub fun w₅ x₅ => wp_lsl (by decide) fun w₆ x₆ => wp_sub fun w₇ x₇ => ?_
  obtain g₇ : ∀ r, r ≠ .r12 → r ≠ .r29 → r ≠ .r30 → r ≠ .r31 → w₇.gpr r = v₁.gpr r := fun r h12 h29 h30 h31 => by
    rw [x₇.other r h31, x₆.other r h12, x₅.other r h31, x₄.other r h30, x₃.other r h30, x₂.other r h30,
      x₁.other r h29]
  obtain r30₄ : w₄.gpr .r30 = BitVec.ofNat 64 nb := by
    rw [x₄.gpr, x₃.gpr, x₂.gpr, x₁.other _ (by decide), x₁.other _ (by decide), v6, v9,
      VG.Offset.ofNat_sub_ofNat (by omega_arith), VG.Offset.ofNat_sub_ofNat (by omega_arith), shr3_ofNat (by omega_arith), hnbe]
  obtain r29₇ : w₇.gpr .r29 = D + BitVec.ofNat 64 f := by
    rw [x₇.other _ (by decide), x₆.other _ (by decide), x₅.other _ (by decide), x₄.other _ (by decide),
      x₃.other _ (by decide), x₂.other _ (by decide), x₁.gpr, r10₁]
  obtain r30₇ : w₇.gpr .r30 = BitVec.ofNat 64 nb := by
    rw [x₇.other _ (by decide), x₆.other _ (by decide), x₅.other _ (by decide), r30₄]
  obtain a6 : w₄.gpr .r6 = BitVec.ofNat 64 len := by
    rw [x₄.other _ (by decide), x₃.other _ (by decide), x₂.other _ (by decide), x₁.other _ (by decide), v6]
  obtain a9 : w₄.gpr .r9 = BitVec.ofNat 64 f := by
    rw [x₄.other _ (by decide), x₃.other _ (by decide), x₂.other _ (by decide), x₁.other _ (by decide), v9]
  obtain r31₇ : w₇.gpr .r31 = BitVec.ofNat 64 rest := by
    rw [x₇.gpr, x₆.other _ (by decide), x₆.gpr, x₅.gpr, x₅.other _ (by decide), r30₄, a6, a9,
      VG.Offset.ofNat_sub_ofNat (by omega_arith), shl3_ofNat (by omega_arith), VG.Offset.ofNat_sub_ofNat (by omega_arith), hreste]
  obtain rd₇ : w₇.rd = u.rd := by rw [x₇.rd, x₆.rd, x₅.rd, x₄.rd, x₃.rd, x₂.rd, x₁.rd, rd₁]
  obtain wr₇ : w₇.wr = u.wr := by rw [x₇.wr, x₆.wr, x₅.wr, x₄.wr, x₃.wr, x₂.wr, x₁.wr, wr₁]
  obtain m₇ : w₇.mem = v₁.mem := by rw [x₇.mem, x₆.mem, x₅.mem, x₄.mem, x₃.mem, x₂.mem, x₁.mem]
  refine wp_ld (a := S + BitVec.ofNat 64 400) (by decide) (by decide)
    (by rw [g₇ _ (by decide) (by decide) (by decide) (by decide), v3]) (stRd _ rd₇ wr₇ 400 8 (by decide))
    fun w₈ x₈ => ?_
  refine wp_ld (a := S + BitVec.ofNat 64 408) (by decide) (by decide)
    (by rw [x₈.other _ (by decide), g₇ _ (by decide) (by decide) (by decide) (by decide), v3])
    (stRd _ (by rw [x₈.rd, rd₇]) (by rw [x₈.wr, wr₇]) 408 8 (by decide)) fun w₉ x₉ => wp_xor fun w₁₀ x₁₀ => ?_
  refine wp_std (a := W + BitVec.ofNat 64 512) (by decide) (by decide)
    (by rw [x₁₀.other _ (by decide), x₉.other _ (by decide), x₈.other _ (by decide),
      g₇ _ (by decide) (by decide) (by decide) (by decide), v5]; rfl)
    (bufW _ (by rw [x₁₀.wr, x₉.wr, x₈.wr, wr₇])) fun w₁₁ x₁₁ => ?_
  refine wp_addi (by decide) (by decide) fun c x₁₂ => wp_nil ?_
  obtain gc : ∀ r, r ≠ .r4 → r ≠ .r7 → r ≠ .r9 → r ≠ .r12 → r ≠ .r29 → r ≠ .r30 → r ≠ .r31 →
      c.gpr r = v₁.gpr r := fun r h4 h7 h9 h12 h29 h30 h31 => by
    rw [x₁₂.other r h4, x₁₁.gpr, x₁₀.other r h7, x₉.other r h9, x₈.other r h7, g₇ r h12 h29 h30 h31]
  obtain c5 : c.gpr .r5 = W := by
    rw [gc _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), v5]
  obtain c4 : c.gpr .r4 = W + BitVec.ofNat 64 512 := by
    rw [x₁₂.gpr, x₁₁.gpr, x₁₀.other _ (by decide), x₉.other _ (by decide), x₈.other _ (by decide),
      g₇ _ (by decide) (by decide) (by decide) (by decide), v5]; rfl
  obtain c3 : c.gpr .r3 = S := by
    rw [gc _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), v3]
  obtain cR : ∀ r, r = .r29 ∨ r = .r30 ∨ r = .r31 → c.gpr r = w₇.gpr r := by
    rintro r (rfl | rfl | rfl) <;>
      rw [x₁₂.other _ (by decide), x₁₁.gpr, x₁₀.other _ (by decide), x₉.other _ (by decide),
        x₈.other _ (by decide)]
  obtain rdc : c.rd = u.rd := by rw [x₁₂.rd, x₁₁.rd, x₁₀.rd, x₉.rd, x₈.rd, rd₇]
  obtain wrc : c.wr = u.wr := by rw [x₁₂.wr, x₁₁.wr, x₁₀.wr, x₉.wr, x₈.wr, wr₇]
  obtain mc : c.mem = v₁.mem.writeW (W + BitVec.ofNat 64 512)
      (v₁.mem.readW (S + BitVec.ofNat 64 400) 64 ^^^ v₁.mem.readW (S + BitVec.ofNat 64 408) 64) := by
    rw [x₁₂.mem, x₁₁.mem, x₁₀.gpr, x₁₀.mem, x₉.gpr, x₉.other _ (by decide), x₈.gpr, x₉.mem, x₈.mem, m₇]
  obtain keyIn : ∀ (t : State), t.rd = u.rd → t.wr = u.wr → InRegions (t.rd ++ t.wr) S 384 := fun t hrd hwr => by
    have := stRd t hrd hwr 0 384 (by decide); simpa using this
  obtain keyScr : Region.Disjoint ⟨S, 384⟩ ⟨W, 640⟩ :=
    (he.stateScr.sub_right (Region.sub_prefix (by decide))).sub_left (Region.sub_prefix (by decide))
  -- The block held back, chained.
  refine WP.seq (encCall_wp c3 c4 c5 (keyIn _ rdc wrc) (L := 688) (by rw [wrc]; exact hWu) (by decide) keyScr
    fun c' rdc' wrc' cc' c'3 c'4 c'5 fc' outc' => ?_)
  obtain rdc'' : c'.rd = u.rd := by rw [rdc', rdc]
  obtain wrc'' : c'.wr = u.wr := by rw [wrc', wrc]
  obtain c'R : ∀ r, r = .r29 ∨ r = .r30 ∨ r = .r31 → c'.gpr r = w₇.gpr r := by
    rintro r (rfl | rfl | rfl) <;> rw [cc' _ (by decide), cR _ (by simp)]
  obtain env : LoopEnv c' S W (D + BitVec.ofNat 64 f) nb :=
    ⟨keyIn _ rdc'' wrc'', ⟨688, by decide, by rw [wrc'']; exact hWu⟩, keyScr, by omega_arith,
      fun j hj => by
        rw [VG.Offset.add_add, rdc'', wrc'']; exact dataIn _ _ (by omega_arith),
      fun j hj => by
        rw [VG.Offset.add_add]; exact dataW _ _ (by omega_arith) _ (List.mem_singleton_self _),
      by omega_arith⟩
  obtain h0 : LoopInv c' S W (D + BitVec.ofNat 64 f) nb 0 c' :=
    ⟨c'3, c'4, c'5, by rw [c'R _ (by simp), r29₇, Nat.mul_zero]; exact (BitVec.add_zero _).symm,
      by rw [c'R _ (by simp), r30₇, Nat.sub_zero], fun _ _ _ _ => rfl, rfl, rfl, Frame.refl _ _, (rfl)⟩
  refine WP.seq (chainLoop_wp env h0 fun t ht => ?_)
  -- The chaining value back to the state, and the bytes to hold back.
  refine WP.seq ?_
  simp only [chainDone, mr]
  obtain tR : ∀ r ∈ preserved, r ≠ .r29 → r ≠ .r30 → t.gpr r = c.gpr r := fun r hr h29 h30 => by
    rw [ht.regs r hr h29 h30, cc' r hr]
  obtain t31 : t.gpr .r31 = BitVec.ofNat 64 rest := by
    rw [tR _ (by decide) (by decide) (by decide), cR _ (by simp), r31₇]
  refine wp_ld (a := W + BitVec.ofNat 64 512) (by decide) (by decide) (by rw [ht.r5]; rfl)
    (by rw [ht.rd, ht.wr, rdc'', wrc'']
        exact ⟨_, List.mem_append_right _ hWu, VG.Offset.contains_base _ (show 512 + 8 ≤ 688 by decide) (by omega_arith)⟩)
    fun t₁ y₁ => ?_
  refine wp_std (a := S + BitVec.ofNat 64 400) (by decide) (by decide) (by rw [y₁.other _ (by decide), ht.r3])
    (by rw [y₁.wr, ht.wr, wrc'']; exact stIn 400 8 (by decide)) fun t₂ y₂ => ?_
  refine wp_addi (by decide) (by decide) fun t₃ y₃ => wp_mr fun t₄ y₄ => wp_mr fun t₅ y₅ => wp_nil ?_
  obtain g₅ : ∀ r, r ≠ .r7 → r ≠ .r10 → r ≠ .r11 → r ≠ .r12 → t₅.gpr r = t.gpr r := fun r h7 h10 h11 h12 => by
    rw [y₅.other r h12, y₄.other r h10, y₃.other r h11, y₂.gpr, y₁.other r h7]
  obtain rd₅ : t₅.rd = u.rd := by rw [y₅.rd, y₄.rd, y₃.rd, y₂.rd, y₁.rd, ht.rd, rdc'']
  obtain wr₅ : t₅.wr = u.wr := by rw [y₅.wr, y₄.wr, y₃.wr, y₂.wr, y₁.wr, ht.wr, wrc'']
  obtain m₅ : t₅.mem = t.mem.writeW (S + BitVec.ofNat 64 400) (t.mem.readW (W + BitVec.ofNat 64 512) 64) := by
    rw [y₅.mem, y₄.mem, y₃.mem, y₂.mem, y₁.gpr, y₁.mem]
  refine copyLoop_wp (src := D + BitVec.ofNat 64 (f + 8 * nb)) (dst := S + BitVec.ofNat 64 408) (n := rest)
    (by omega_arith)
    (by rw [y₅.other _ (by decide), y₄.gpr, y₃.other _ (by decide), y₂.gpr, y₁.other _ (by decide), ht.r29,
      VG.Offset.add_add])
    (by rw [y₅.other _ (by decide), y₄.other _ (by decide), y₃.gpr, y₂.gpr, y₁.other _ (by decide), ht.r3])
    (by rw [y₅.gpr, y₄.other _ (by decide), y₃.other _ (by decide), y₂.gpr, y₁.other _ (by decide), t31])
    (fun i hi => by rw [rd₅, wr₅, VG.Offset.add_add]; exact dataIn _ _ (by omega_arith))
    (fun i hi => by rw [wr₅, VG.Offset.add_add]; exact stIn _ _ (by omega_arith))
    (fun i hi i' hi' => by
      rw [VG.Offset.add_add, VG.Offset.add_add]; exact state_ne_data he.dataState hD (by omega_arith) (by omega_arith))
    fun v hv => ?_
  -- The memory.
  obtain FR : ∀ r ∈ [(⟨S + BitVec.ofNat 64 400, 16⟩ : Region)],
      r ∈ [(⟨S + BitVec.ofNat 64 400, 16⟩ : Region), ⟨W, 520⟩] := fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact List.mem_cons_self
  obtain FW : ∀ r ∈ [(⟨W, 520⟩ : Region)], r ∈ [(⟨S + BitVec.ofNat 64 400, 16⟩ : Region), ⟨W, 520⟩] := fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; simp
  obtain s400 : (⟨S + BitVec.ofNat 64 400, 16⟩ : Region).Contains (S + BitVec.ofNat 64 400) (64 / 8) :=
    VG.Offset.contains_base _ (show 0 + 64 / 8 ≤ 16 by decide) (by decide) |> fun h => by simpa using h
  obtain Fc : Frame [⟨W, 520⟩] v₁.mem c.mem := by
    rw [mc]
    exact (Frame.refl _ _).writeW List.mem_cons_self _
      (VG.Offset.contains_base _ (show 512 + 64 / 8 ≤ 520 by decide) (by omega_arith))
  obtain Fc' : Frame [⟨S + BitVec.ofNat 64 400, 16⟩, ⟨W, 520⟩] u.mem c'.mem :=
    ((m₁S.mono FR).trans (Fc.mono FW)).trans (fc'.mono FW)
  obtain Ft : Frame [⟨S + BitVec.ofNat 64 400, 16⟩, ⟨W, 520⟩] u.mem t.mem := Fc'.trans (ht.frame.mono FW)
  obtain F₅ : Frame [⟨S + BitVec.ofNat 64 400, 16⟩, ⟨W, 520⟩] u.mem t₅.mem := by
    rw [m₅]; exact Ft.writeW List.mem_cons_self _ s400
  obtain Fv : Frame [⟨S + BitVec.ofNat 64 400, 16⟩, ⟨W, 520⟩] u.mem v.mem := F₅.trans fun x hx =>
    hv.rest x fun i hi e => hx _ List.mem_cons_self (by
      rw [e, VG.Offset.add_add]
      exact VG.Offset.contains _ (show 400 ≤ 408 + i by omega_arith) (show 408 + i + 1 ≤ 400 + 16 by omega_arith) (by omega_arith))
  obtain dataD : ∀ a n, a + n ≤ len → ∀ r ∈ [(⟨S + BitVec.ofNat 64 400, 16⟩ : Region), ⟨W, 520⟩],
      Region.Disjoint ⟨D + BitVec.ofNat 64 a, n⟩ r := fun a n h r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact dataS a n h
    · exact dataW a n h _ (List.mem_singleton_self _)
  obtain keyD : ∀ r ∈ [(⟨S + BitVec.ofNat 64 400, 16⟩ : Region), ⟨W, 520⟩], (⟨S, 384⟩ : Region).Disjoint r :=
    fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact keyS _ (List.mem_singleton_self _)
      · exact keyW _ (List.mem_singleton_self _)
  obtain dataEq : ∀ {m : Mem}, Frame [⟨S + BitVec.ofNat 64 400, 16⟩, ⟨W, 520⟩] u.mem m → ∀ a n, a + n ≤ len →
      Spec.Aes.bytesAt m (D + BitVec.ofNat 64 a) n = Spec.Aes.bytesAt u.mem (D + BitVec.ofNat 64 a) n :=
    fun hF a n h => List.map_congr_left fun i hi => hF.bytes (R := ⟨D + BitVec.ofNat 64 a, n⟩) (dataD a n h)
      (by show n ≤ 2 ^ 64; omega_arith) (List.mem_range.mp hi)
  refine ⟨⟨fun r hr h29 h30 h31 => ?_, ?_, by rw [hv.rd, rd₅], by rw [hv.wr, wr₅], ?_⟩, ⟨fun i hi => ?_, ?_, ?_⟩⟩
  · obtain ⟨h0, -, h4, -, -, h7, -, h9, h10, h11, h12⟩ := preserved_ne r hr
    rw [hv.regs r h0 h10 h11 h12, g₅ r h7 h10 h11 h12, tR r hr h29 h30, gc r h4 h7 h9 h12 h29 h30 h31,
      g₁ r h0 h10 h11 h12]
  · rw [hv.regs _ (by decide) (by decide) (by decide) (by decide), g₅ _ (by decide) (by decide) (by decide)
      (by decide), ht.r5]
  · exact Fv.sub fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨_, List.mem_cons_self, VG.Offset.sub_base _ (by decide)⟩
      · exact ⟨_, by simp, fun _ h => h⟩
  · exact Fv.bytes (R := ⟨S, 400⟩) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact VG.Offset.base_disjoint _ (by decide) (by omega_arith)
      · exact (he.stateScr.sub_right (Region.sub_prefix (by decide))).sub_left (Region.sub_prefix (by decide)))
      (by show 400 ≤ 2 ^ 64; decide) hi
  · -- The chaining value.
    rw [hf, hnb]
    obtain e400 : Spec.Aes.bytesAt v.mem (S + BitVec.ofNat 64 400) 8 = Spec.Aes.bytesAt t₅.mem (S + BitVec.ofNat 64 400) 8 :=
      Proof.CmacTripleDes.Stream.bytesAt_congr fun i hi => hv.rest _ fun i' hi' => by
        rw [VG.Offset.add_add, VG.Offset.add_add]; exact VG.Offset.add_ofNat_ne _ (by omega_arith) (by omega_arith) (by omega_arith)
    obtain kc : Spec.TripleDes.scheduleAt c.mem S = Spec.TripleDes.scheduleAt u.mem S :=
      Proof.TripleDes.scheduleAt_eq_of_frame _ ((m₁S.mono FR).trans (Fc.mono FW)) keyD
    obtain kc' : Spec.TripleDes.scheduleAt c'.mem S = Spec.TripleDes.scheduleAt u.mem S :=
      Proof.TripleDes.scheduleAt_eq_of_frame _ Fc' keyD
    obtain bl : Spec.Cmac.blocksAt c'.mem (D + BitVec.ofNat 64 f) 8 nb =
        Spec.Cmac.blocksAt u.mem (D + BitVec.ofNat 64 f) 8 nb :=
      List.map_congr_left fun j hj => by
        obtain hj := List.mem_range.mp hj
        rw [VG.Offset.add_add]; exact dataEq Fc' _ _ (by omega_arith)
    obtain c400 : Spec.Aes.bytesAt v₁.mem (S + BitVec.ofNat 64 400) 8 = Spec.Aes.bytesAt u.mem (S + BitVec.ofNat 64 400) 8 :=
      Proof.CmacTripleDes.Stream.bytesAt_congr fun i hi => cp₁.rest _ fun i' hi' => by
        rw [VG.Offset.add_add, VG.Offset.add_add]; exact VG.Offset.add_ofNat_ne _ (by omega_arith) (by omega_arith) (by omega_arith)
    rw [e400, m₅, ← Proof.Cmac.le8_readW, Mem.readW_writeW_self64, Proof.Cmac.le8_readW, ht.buf, enc_bytes outc', kc',
      kc, bl, mc, ← Proof.Cmac.le8_readW, Mem.readW_writeW_self64, Proof.Cmac.le8_xor, Proof.Cmac.le8_readW,
      Proof.Cmac.le8_readW, c400, heldB, Proof.Cmac.chain_append, Proof.Cmac.chain_single]
  · -- The bytes held back.
    rw [hf, hnb, hr]
    refine List.map_congr_left fun i hi => ?_
    obtain hi := List.mem_range.mp hi
    rw [hv.copied i hi]
    exact F₅.bytes (R := ⟨D + BitVec.ofNat 64 (f + 8 * nb), rest⟩) (dataD _ _ (by omega_arith)) (by show rest ≤ 2 ^ 64; omega_arith) hi

end VG.Proof.CmacTripleDes.Stream.PPC64LE

end

end


/-!
# Streaming TDEA-CMAC on PPC64LE: `absorb` is correct

`absorb_wp`: `absorb` appends the data to the message the state
represents, through the path the flag chooses (`fill_spec`, `chain_spec`),
and restores the registers it saved.
-/

@[expose] public section

namespace VG.Proof.CmacTripleDes.Stream.PPC64LE

open VG VG.PPC64LE VG.Impl.CmacTripleDes.Stream.PPC64LE
open VG.Proof.CmacTripleDes.Stream (held nblocks)

theorem take_bytesAt (m : Mem) (p : Addr) {k n : Nat} (h : k ≤ n) :
    (Spec.Aes.bytesAt m p n).take k = Spec.Aes.bytesAt m p k := by
  simp only [Spec.Aes.bytesAt, ← List.map_take, List.take_range, Nat.min_eq_left h]

theorem fill_spec {m m' : Mem} {S D : Addr} {key msg : List Byte} {len : Nat}
    (hr : Spec.Cmac.tdesRepr m S key msg) (hl : len ≤ 8 - held msg.length)
    (hc : Copied m D (S + BitVec.ofNat 64 (408 + held msg.length)) len m') :
    Spec.Cmac.tdesRepr m' S key (msg ++ Spec.Aes.bytesAt m D len) := by
  obtain hh := Proof.CmacTripleDes.Stream.held_le msg.length
  obtain ne : ∀ a, a < 408 + held msg.length → ∀ i < len,
      S + BitVec.ofNat 64 a ≠ S + BitVec.ofNat 64 (408 + held msg.length) + BitVec.ofNat 64 i := fun a ha i hi => by
    rw [VG.Offset.add_add]; exact VG.Offset.add_ofNat_ne _ (by omega_arith) (by omega_arith) (by omega_arith)
  refine Proof.CmacTripleDes.Stream.repr_fill hr (fun i hi => hc.rest _ (ne i (by omega_arith)))
    (by simp [Spec.Aes.bytesAt]; exact hl) ?_ ?_
  · rw [show S + 400 = S + BitVec.ofNat 64 400 from rfl]
    exact Proof.CmacTripleDes.Stream.bytesAt_congr fun i hi => by
      rw [VG.Offset.add_add]; exact hc.rest _ (ne _ (by omega_arith))
  · have hlen : (Spec.Aes.bytesAt m D len).length = len := by simp [Spec.Aes.bytesAt]
    rw [hlen, show S + 408 = S + BitVec.ofNat 64 408 from rfl, Proof.Cmac.Stream.bytesAt_append, VG.Offset.add_add]
    congr 1
    · exact Proof.CmacTripleDes.Stream.bytesAt_congr fun i hi => by
        rw [VG.Offset.add_add]; exact hc.rest _ (ne _ (by omega_arith))
    · exact List.map_congr_left fun i hi => hc.copied i (List.mem_range.mp hi)

theorem chain_spec {m m' : Mem} {S D : Addr} {key msg : List Byte} {len : Nat}
    (hr : Spec.Cmac.tdesRepr m S key msg) (hl : 8 - held msg.length < len)
    (hc : ChainMem m S D len (held msg.length) m') :
    Spec.Cmac.tdesRepr m' S key (msg ++ Spec.Aes.bytesAt m D len) := by
  obtain hh := Proof.CmacTripleDes.Stream.held_le msg.length
  obtain hlen : (Spec.Aes.bytesAt m D len).length = len := by simp [Spec.Aes.bytesAt]
  have hnb : nblocks msg.length len = nbOf len (8 - held msg.length) := rfl
  obtain hnb8 : 8 * nbOf len (8 - held msg.length) ≤ len - (8 - held msg.length) - 1 := by
    show 8 * ((len - (8 - held msg.length) - 1) / 8) ≤ _; omega_arith
  refine Proof.CmacTripleDes.Stream.repr_chain hr hc.key (by rw [hlen]; exact hl) ?_ ?_
  · rw [show S + 400 = S + BitVec.ofNat 64 400 from rfl, show S + 408 = S + BitVec.ofNat 64 408 from rfl,
      hc.chain, hr.2.1, hlen, hnb, take_bytesAt _ _ (by omega_arith), ← Proof.Cmac.Stream.bytesAt_offset _ _ (by omega_arith),
      Proof.CmacTripleDes.Stream.blocksAt_eq]
    rfl
  · rw [show S + 408 = S + BitVec.ofNat 64 408 from rfl, hlen, hnb, List.drop_drop]
    have e := hc.held
    rw [Proof.Cmac.Stream.bytesAt_offset m D (n := len) (by
      show 8 - held msg.length + 8 * nbOf len (8 - held msg.length) +
        (len - (8 - held msg.length) - 8 * nbOf len (8 - held msg.length)) ≤ len; omega_arith)] at e
    exact e.trans (List.take_of_length_le (by
      rw [List.length_drop, hlen]
      show len - _ ≤ len - (8 - held msg.length) - 8 * nbOf len (8 - held msg.length); omega_arith))

/-- What `absorb` leaves, for a state that represents a message of `count`
bytes. -/
def AbsorbOut (m : Mem) (S D : Addr) (count len : Nat) (m' : Mem) : Prop :=
  ∀ key msg, Spec.Cmac.tdesRepr m S key msg → msg.length = count →
    Spec.Cmac.tdesRepr m' S key (msg ++ Spec.Aes.bytesAt m D len)

theorem absorb_wp (s : State) (hp : AbsorbPre s) :
    WP isa absorb s fun f => (∀ r ∈ preserved, f.gpr r = s.gpr r) ∧ f.lr = s.lr ∧
      AbsorbOut s.mem (s.gpr .r3) (s.gpr .r5) (s.gpr .r4).toNat (s.gpr .r6).toNat f.mem := by
  obtain hW : (⟨s.gpr .r7, 688⟩ : Region) ∈ s.wr := by rw [hp.wr]; simp
  obtain hS : (⟨s.gpr .r3, 416⟩ : Region) ∈ s.wr := by rw [hp.wr]; simp
  obtain hDr : (⟨s.gpr .r5, (s.gpr .r6).toNat⟩ : Region) ∈ s.rd := by rw [hp.rd]; simp
  have hfW := hp.scrFit
  obtain hh := Proof.CmacTripleDes.Stream.held_le (s.gpr .r4).toNat
  obtain cW : ∀ off, off + 8 ≤ 688 → (⟨s.gpr .r7, 688⟩ : Region).Contains (s.gpr .r7 + BitVec.ofNat 64 off) (64 / 8) :=
    fun off h => VG.Offset.contains_base _ h (by omega_arith)
  unfold absorb
  refine WP.seq ?_
  rw [← List.append_nil absorbSave]
  refine absorbSave_wp hp fun t ht => wp_nil ?_
  obtain F0 : Frame [⟨s.gpr .r7, 688⟩] s.mem t.mem := by
    rw [ht.mem]
    exact ((((Frame.refl _ _).writeW List.mem_cons_self _ (cW lrOff (by decide))).writeW List.mem_cons_self _
      (cW r29Off (by decide))).writeW List.mem_cons_self _ (cW r30Off (by decide))).writeW List.mem_cons_self _
      (cW r31Off (by decide))
  refine WP.seq (heldCode_wp (s.gpr .r4).isLt (by rw [ht.regs _ (by decide) (by decide) (by decide),
    BitVec.ofNat_toNat, BitVec.setWidth_eq]) fun t₁ h8 g₁ m₁ rd₁ wr₁ => ?_)
  refine WP.seq ?_
  rw [← List.append_nil absorbFlag]
  refine flag_wp hh (s.gpr .r6).isLt (len := (s.gpr .r6).toNat) h8 (by
    rw [g₁ _ (by decide) (by decide), ht.regs _ (by decide) (by decide) (by decide), BitVec.ofNat_toNat,
      BitVec.setWidth_eq]) fun u r9 ev gu mu rdu wru => wp_nil ?_
  obtain gu' : ∀ r, r ≠ .r0 → r ≠ .r5 → r ≠ .r8 → r ≠ .r9 → r ≠ .r10 → r ≠ .r11 → r ≠ .r29 → u.gpr r = s.gpr r :=
    fun r h0 h5 h8 h9 h10 h11 h29 => by rw [gu r h9 h10 h11, g₁ r h8 h9, ht.regs r h0 h5 h29]
  obtain rdu' : u.rd = s.rd := by rw [rdu, rd₁, ht.rd]
  obtain wru' : u.wr = s.wr := by rw [wru, wr₁, ht.wr]
  obtain he : PathEnv u (s.gpr .r3) (s.gpr .r5) (s.gpr .r7) (s.gpr .r6).toNat (held (s.gpr .r4).toNat) :=
    { r3 := gu' _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      r5 := by rw [gu _ (by decide) (by decide) (by decide), g₁ _ (by decide) (by decide), ht.r5]
      r6 := by
        rw [gu' _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
          BitVec.ofNat_toNat, BitVec.setWidth_eq]
      r8 := by rw [gu _ (by decide) (by decide) (by decide), h8]
      r9 := r9
      r29 := by rw [gu _ (by decide) (by decide) (by decide), g₁ _ (by decide) (by decide), ht.r29]
      hh := hh
      lenLt := (s.gpr .r6).isLt
      data := by rw [rdu']; exact hDr
      state := by rw [wru']; exact hS
      scr := by rw [wru']; exact hW
      dataState := hp.dataState
      dataScr := hp.dataScr
      stateScr := hp.stateScr
      stateFit := hp.stateFit
      dataFit := hp.dataFit
      scrFit := hp.scrFit }
  -- The data and the state's bytes are as they were before the saves.
  obtain hmu : u.mem = t.mem := by rw [mu, m₁]
  obtain stEq : ∀ i < 416, u.mem (s.gpr .r3 + BitVec.ofNat 64 i) = s.mem (s.gpr .r3 + BitVec.ofNat 64 i) :=
    fun i hi => by
      rw [hmu]; exact F0.bytes (R := ⟨s.gpr .r3, 416⟩) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact hp.stateScr) (by show 416 ≤ 2 ^ 64; decide) hi
  obtain dEq : Spec.Aes.bytesAt u.mem (s.gpr .r5) (s.gpr .r6).toNat = Spec.Aes.bytesAt s.mem (s.gpr .r5) (s.gpr .r6).toNat :=
    List.map_congr_left fun i hi => by
      rw [hmu]; exact F0.bytes (R := ⟨s.gpr .r5, (s.gpr .r6).toNat⟩) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact hp.dataScr)
        (by show (s.gpr .r6).toNat ≤ 2 ^ 64; omega_arith) (List.mem_range.mp hi)
  obtain hb : WP isa (.ite (.nonzero .d .r10) chainPath fillPath) u fun v =>
      PathOut u (s.gpr .r3) (s.gpr .r7) v ∧
        AbsorbOut s.mem (s.gpr .r3) (s.gpr .r5) (s.gpr .r4).toNat (s.gpr .r6).toNat v.mem := by
    by_cases hc : 8 - held (s.gpr .r4).toNat < (s.gpr .r6).toNat
    · refine WP.ite true (by rw [ev, decide_eq_true hc]) (fun _ => ?_) (fun h => by cases h)
      refine WP.mono (chain_wp he hc) fun v ⟨po, cm⟩ => ⟨po, fun key msg hr hn => ?_⟩
      rw [← dEq]
      rw [← hn] at hc cm
      exact chain_spec (Proof.CmacTripleDes.Stream.repr_congr_416 stEq hr) hc cm
    · refine WP.ite false (by rw [ev, decide_eq_false hc]) (fun h => by cases h) fun _ => ?_
      refine WP.mono (fill_wp he (by omega_arith)) fun v ⟨po, cp⟩ => ⟨po, fun key msg hr hn => ?_⟩
      rw [← dEq]
      rw [← hn] at hc cp
      exact fill_spec (Proof.CmacTripleDes.Stream.repr_congr_416 stEq hr) (by omega_arith) cp
  refine WP.seq (WP.mono hb fun v hv => ?_)
  obtain ⟨po, out⟩ := hv
  -- The saved registers, back.
  obtain slot : ∀ off, 528 ≤ off → off + 8 ≤ 688 →
      v.mem.readW (s.gpr .r7 + BitVec.ofNat 64 off) 64 = t.mem.readW (s.gpr .r7 + BitVec.ofNat 64 off) 64 :=
    fun off h1 h2 => by
      rw [po.frame.readW (Region.contains_self _ _) (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact (hp.stateScr.sub_right (VG.Offset.sub_base _ h2)).symm
        · exact VG.Offset.disjoint_base _ (by omega_arith) (by omega_arith)) (by decide), hmu]
  obtain hR : ∀ (w : State), w.rd = s.rd → w.wr = s.wr → ∀ off, off + 8 ≤ 688 →
      InRegions (w.rd ++ w.wr) (s.gpr .r7 + BitVec.ofNat 64 off) 8 := fun w hrd hwr off h => by
    rw [hrd, hwr]; exact ⟨_, List.mem_append_right _ hW, VG.Offset.contains_base _ h (by omega_arith)⟩
  have v5 : v.gpr .r5 = s.gpr .r7 := po.r5
  obtain rdv : v.rd = s.rd := by rw [po.rd, rdu']
  obtain wrv : v.wr = s.wr := by rw [po.wr, wru']
  simp only [absorbRestore]
  refine wp_ld (a := s.gpr .r7 + BitVec.ofNat 64 lrOff) (by decide) (by decide) (by rw [v5])
    (hR _ rdv wrv _ (by decide)) fun w₁ x₁ => ?_
  refine wp_ld (a := s.gpr .r7 + BitVec.ofNat 64 r29Off) (by decide) (by decide) (by rw [x₁.other _ (by decide), v5])
    (hR _ (by rw [x₁.rd, rdv]) (by rw [x₁.wr, wrv]) _ (by decide)) fun w₂ x₂ => ?_
  refine wp_ld (a := s.gpr .r7 + BitVec.ofNat 64 r30Off) (by decide) (by decide)
    (by rw [x₂.other _ (by decide), x₁.other _ (by decide), v5])
    (hR _ (by rw [x₂.rd, x₁.rd, rdv]) (by rw [x₂.wr, x₁.wr, wrv]) _ (by decide)) fun w₃ x₃ => ?_
  refine wp_ld (a := s.gpr .r7 + BitVec.ofNat 64 r31Off) (by decide) (by decide)
    (by rw [x₃.other _ (by decide), x₂.other _ (by decide), x₁.other _ (by decide), v5])
    (hR _ (by rw [x₃.rd, x₂.rd, x₁.rd, rdv]) (by rw [x₃.wr, x₂.wr, x₁.wr, wrv]) _ (by decide)) fun w₄ x₄ =>
      wp_mtlr (wp_nil ?_)
  obtain mw : w₄.mem = v.mem := by rw [x₄.mem, x₃.mem, x₂.mem, x₁.mem]
  obtain sl : ∀ off, (off = lrOff ∨ off = r29Off ∨ off = r30Off ∨ off = r31Off) →
      v.mem.readW (s.gpr .r7 + BitVec.ofNat 64 off) 64 = t.mem.readW (s.gpr .r7 + BitVec.ofNat 64 off) 64 := by
    rintro off (rfl | rfl | rfl | rfl) <;> exact slot _ (by decide) (by decide)
  obtain dj : ∀ a b, a + 8 ≤ b ∨ b + 8 ≤ a → b + 8 ≤ 688 → a + 8 ≤ 688 →
      Region.Disjoint ⟨s.gpr .r7 + BitVec.ofNat 64 a, 8⟩ ⟨s.gpr .r7 + BitVec.ofNat 64 b, 8⟩ :=
    fun a b h hb ha => VG.Offset.disjoint _ h (by omega_arith) (by omega_arith)
  refine ⟨fun r hr => ?_, ?_, ?_⟩
  · show w₄.gpr r = _
    by_cases e31 : r = .r31
    · subst e31
      rw [x₄.gpr, x₃.mem, x₂.mem, x₁.mem, sl _ (by simp), ht.mem, Mem.readW_writeW_self64]
    by_cases e30 : r = .r30
    · subst e30
      rw [x₄.other _ (by decide), x₃.gpr, x₂.mem, x₁.mem, sl _ (by simp), ht.mem,
        readW_sep64 (dj _ _ (by decide) (by decide) (by decide)), Mem.readW_writeW_self64]
    by_cases e29 : r = .r29
    · subst e29
      rw [x₄.other _ (by decide), x₃.other _ (by decide), x₂.gpr, x₁.mem, sl _ (by simp), ht.mem,
        readW_sep64 (dj _ _ (by decide) (by decide) (by decide)),
        readW_sep64 (dj _ _ (by decide) (by decide) (by decide)), Mem.readW_writeW_self64]
    obtain ⟨h0, -, -, h5, -, -, h8, h9, h10, h11, -⟩ := preserved_ne r hr
    rw [x₄.other r e31, x₃.other r e30, x₂.other r e29, x₁.other r h0, po.regs r hr e29 e30 e31,
      gu' r h0 h5 h8 h9 h10 h11 e29]
  · show w₄.gpr .r0 = _
    rw [x₄.other _ (by decide), x₃.other _ (by decide), x₂.other _ (by decide), x₁.gpr, sl _ (by simp), ht.mem,
      readW_sep64 (dj _ _ (by decide) (by decide) (by decide)),
      readW_sep64 (dj _ _ (by decide) (by decide) (by decide)),
      readW_sep64 (dj _ _ (by decide) (by decide) (by decide)), Mem.readW_writeW_self64]
  · show AbsorbOut _ _ _ _ _ w₄.mem
    rw [mw]; exact out

end VG.Proof.CmacTripleDes.Stream.PPC64LE

end

end

/-! ### `CmacTripleDes.Stream.PPC64LE.Finish`, which only this module used -/

section

/-!
# Streaming TDEA-CMAC on PPC64LE: `finish`

`finish_wp`: `finish` writes to `out` the cipher, under the schedule in the
state, of the chaining value XORed with the last block (`lastBlock`) of the
bytes held back, which `held count` gives the number of: `K1` XORed with
them if they are a complete block, else `K2` XORed with them padded. The
padded block is built in the working space (`padOff`): zeroed, the bytes
held back copied onto it (`copyLoop_wp`), and `0x80` after them
(`padded_bytes8`). `finish_spec` is then `tdesFinishPost`.
-/

@[expose] public section

namespace VG.Proof.CmacTripleDes.Stream.PPC64LE

open VG VG.PPC64LE VG.Impl.CmacTripleDes.Stream.PPC64LE
open VG.Proof.Cmac (le8)
open VG.Proof.CmacTripleDes.Stream (held)

/-- `finish`'s precondition, with the working space of 640 bytes at `r6`. -/
structure FinishPre (s : State) : Prop where
  wr : s.wr = [⟨s.gpr .r3, 416⟩, ⟨s.gpr .r5, 8⟩, ⟨s.gpr .r6, 640⟩]
  stateOut : Region.Disjoint ⟨s.gpr .r3, 416⟩ ⟨s.gpr .r5, 8⟩
  stateScr : Region.Disjoint ⟨s.gpr .r3, 416⟩ ⟨s.gpr .r6, 640⟩
  outScr : Region.Disjoint ⟨s.gpr .r5, 8⟩ ⟨s.gpr .r6, 640⟩
  stateFit : (s.gpr .r3).toNat + 416 ≤ 2 ^ 64
  outFit : (s.gpr .r5).toNat + 8 ≤ 2 ^ 64
  scrFit : (s.gpr .r6).toNat + 640 ≤ 2 ^ 64

/-- The last block `finish` enciphers: the chaining value XORed with the
last block of the bytes held back. -/
abbrev finBlock (m : Mem) (S : Addr) (h : Nat) : List Byte :=
  Spec.Cmac.xor (Spec.Aes.bytesAt m (S + BitVec.ofNat 64 400) 8)
    (Spec.Cmac.lastBlock 8 (Spec.Aes.bytesAt m (S + BitVec.ofNat 64 384) 8)
      (Spec.Aes.bytesAt m (S + BitVec.ofNat 64 392) 8) (Spec.Aes.bytesAt m (S + BitVec.ofNat 64 408) h))

theorem xor3 (a b c : BitVec 64) : a ^^^ b ^^^ c = c ^^^ (b ^^^ a) := by
  rw [BitVec.xor_comm (a ^^^ b), BitVec.xor_comm a]

theorem le8_xor3 (a b c : BitVec 64) : le8 (a ^^^ b ^^^ c) = Spec.Cmac.xor (le8 c) (Spec.Cmac.xor (le8 b) (le8 a)) := by
  rw [xor3, Proof.Cmac.le8_xor, Proof.Cmac.le8_xor]

/-- After the branch: the block to encipher in the buffer, the memory but
the working space unchanged, and the registers but the temporaries. -/
structure BufReady (t u : State) (S B : Addr) (h : Nat) : Prop where
  buf : Spec.Aes.bytesAt u.mem (B + BitVec.ofNat 64 512) 8 = finBlock t.mem S h
  frame : Frame [⟨B, 528⟩] t.mem u.mem
  regs : ∀ r, r ≠ .r0 → r ≠ .r7 → r ≠ .r9 → r ≠ .r10 → r ≠ .r11 → r ≠ .r12 → u.gpr r = t.gpr r
  rd : u.rd = t.rd
  wr : u.wr = t.wr

theorem complete_wp {t : State} {S B : Addr} (h3 : t.gpr .r3 = S) (h5 : t.gpr .r5 = B)
    (hS : (⟨S, 416⟩ : Region) ∈ t.wr) (hW : (⟨B, 640⟩ : Region) ∈ t.wr) :
    WP isa (.block complete) t fun u => BufReady t u S B 8 := by
  obtain inS : ∀ off, off + 8 ≤ 416 → InRegions (t.rd ++ t.wr) (S + BitVec.ofNat 64 off) 8 := fun off h =>
    ⟨_, List.mem_append_right _ hS, VG.Offset.contains_base _ h (by omega_arith)⟩
  simp only [complete]
  refine wp_ld (a := S + BitVec.ofNat 64 408) (by decide) (by decide) (by rw [h3]) (inS 408 (by decide))
    fun s₁ u₁ => ?_
  refine wp_ld (a := S + BitVec.ofNat 64 384) (by decide) (by decide) (by rw [u₁.other _ (by decide), h3])
    (by rw [u₁.rd, u₁.wr]; exact inS 384 (by decide)) fun s₂ u₂ => wp_xor fun s₃ u₃ => ?_
  refine wp_ld (a := S + BitVec.ofNat 64 400) (by decide) (by decide)
    (by rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), h3])
    (by rw [u₃.rd, u₃.wr, u₂.rd, u₂.wr, u₁.rd, u₁.wr]; exact inS 400 (by decide)) fun s₄ u₄ => wp_xor fun s₅ u₅ => ?_
  refine wp_std (a := B + BitVec.ofNat 64 512) (by decide) (by decide)
    (by rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide),
      u₁.other _ (by decide), h5]; rfl)
    (by rw [u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]; exact scr_in hW (by decide)) fun s₆ u₆ => wp_nil ?_
  obtain m₅ : s₅.mem = t.mem := by rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  obtain w : s₅.gpr .r7 = t.mem.readW (S + BitVec.ofNat 64 408) 64 ^^^ t.mem.readW (S + BitVec.ofNat 64 384) 64 ^^^
      t.mem.readW (S + BitVec.ofNat 64 400) 64 := by
    obtain a3 : s₃.gpr .r7 = t.mem.readW (S + BitVec.ofNat 64 408) 64 ^^^ t.mem.readW (S + BitVec.ofNat 64 384) 64 := by
      rw [u₃.gpr, u₂.other _ (by decide), u₁.gpr, u₂.gpr, u₁.mem]
    obtain b4 : s₄.gpr .r9 = t.mem.readW (S + BitVec.ofNat 64 400) 64 := by rw [u₄.gpr, u₃.mem, u₂.mem, u₁.mem]
    rw [u₅.gpr, u₄.other _ (by decide), a3, b4]
  refine ⟨?_, ?_, fun r h0 h7 h9 _ _ _ => ?_, by rw [u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd],
    by rw [u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]⟩
  · rw [u₆.mem, m₅, w, ← Proof.Cmac.le8_readW, Mem.readW_writeW_self64, le8_xor3, Proof.Cmac.le8_readW,
      Proof.Cmac.le8_readW, Proof.Cmac.le8_readW, finBlock, Spec.Cmac.lastBlock,
      ite_eq_left (by simp [Spec.Aes.bytesAt] : (Spec.Aes.bytesAt t.mem (S + BitVec.ofNat 64 408) 8).length = 8)]
  · rw [u₆.mem, m₅]
    exact (Frame.refl _ _).writeW List.mem_cons_self _ (VG.Offset.contains_base _ (show 512 + 64 / 8 ≤ 528 by decide)
      (by decide))
  · rw [u₆.gpr, u₅.other r h7, u₄.other r h9, u₃.other r h7, u₂.other r h9, u₁.other r h7]

theorem sub_add_ofNat (C : Addr) {k : Nat} (hk : k < 2 ^ 64) : (C + BitVec.ofNat 64 k - C).toNat = k :=
  Mem.sub_ofNat_toNat C hk

theorem add_ofNat_inj (C : Addr) {i j : Nat} (hi : i < 2 ^ 64) (hj : j < 2 ^ 64)
    (h : C + BitVec.ofNat 64 i = C + BitVec.ofNat 64 j) : i = j := by
  have := congrArg (fun a => (a - C).toNat) h
  simp only [sub_add_ofNat C hi, sub_add_ofNat C hj] at this
  exact this

/-- The padded block: the bytes copied onto zeros, and `0x80` after them, as
`padded_bytes8` has it. -/
theorem pad_bytes {m₀ mc : Mem} {S C : Addr} {h : Nat} (hh : h < 8)
    (hcopied : ∀ i < h, mc (C + BitVec.ofNat 64 i) = (m₀.writeW C (0 : BitVec 64)) (S + BitVec.ofNat 64 (408 + i)))
    (hrest : ∀ x, (∀ i < h, x ≠ C + BitVec.ofNat 64 i) → mc x = (m₀.writeW C (0 : BitVec 64)) x)
    (hsep : ∀ i < h, (m₀.writeW C (0 : BitVec 64)) (S + BitVec.ofNat 64 (408 + i)) = m₀ (S + BitVec.ofNat 64 (408 + i))) :
    Spec.Aes.bytesAt (mc.writeW (C + BitVec.ofNat 64 h) ((BitVec.ofNat 64 0x80).setWidth 8)) C 8 =
      Spec.Aes.bytesAt m₀ (S + BitVec.ofNat 64 408) h ++ [0x80] ++
        Spec.Cmac.zeros (8 - (Spec.Aes.bytesAt m₀ (S + BitVec.ofNat 64 408) h).length - 1) := by
  obtain hlen : (Spec.Aes.bytesAt m₀ (S + BitVec.ofNat 64 408) h).length = h := by simp [Spec.Aes.bytesAt]
  rw [← padded_bytes8 (m₀.writeW C (0 : BitVec 64)) C _ (by rw [hlen]; exact hh) (by
      rw [← Proof.Cmac.le8_readW, Mem.readW_writeW_self64, Proof.Cmac.le8_zero]), hlen]
  refine List.map_congr_left fun k hk => ?_
  obtain hk := List.mem_range.mp hk
  rw [VG.WriteBytes.writeW8_apply, VG.WriteBytes.writeW8_apply,
    show ((BitVec.ofNat 64 0x80).setWidth 8 : Byte) = 0x80 from rfl]
  split
  · rfl
  · rename_i hne
    simp only [VG.WriteBytes.writeBytes, sub_add_ofNat C (show k < 2 ^ 64 by omega_arith), hlen]
    by_cases hkh : k < h
    · rw [ite_eq_left hkh, hcopied k hkh, hsep k hkh, Proof.Cmac.getD_bytesAt _ _ hkh, VG.Offset.add_add]
    · rw [ite_eq_right hkh, hrest _ fun i hi e => hkh (by
        have := add_ofNat_inj C (show k < 2 ^ 64 by omega_arith) (show i < 2 ^ 64 by omega_arith) e; omega_arith)]

theorem padded_wp {t : State} {S B : Addr} {h : Nat} (hh : h < 8) (h3 : t.gpr .r3 = S) (h5 : t.gpr .r5 = B)
    (h8 : t.gpr .r8 = BitVec.ofNat 64 h)
    (hS : (⟨S, 416⟩ : Region) ∈ t.wr) (hW : (⟨B, 640⟩ : Region) ∈ t.wr) (hd : Region.Disjoint ⟨S, 416⟩ ⟨B, 640⟩) :
    WP isa padded t fun u => BufReady t u S B h := by
  obtain inS : ∀ off, off + 8 ≤ 416 → InRegions (t.rd ++ t.wr) (S + BitVec.ofNat 64 off) 8 := fun off h =>
    ⟨_, List.mem_append_right _ hS, VG.Offset.contains_base _ h (by omega_arith)⟩
  -- The state's bytes and the working space's are apart.
  obtain sep1 : ∀ i j, i < 416 → j < 640 → S + BitVec.ofNat 64 i ≠ B + BitVec.ofNat 64 j := fun i j hi hj e =>
    hd _ (VG.Offset.contains_base _ (show i + 1 ≤ 416 by omega_arith) (by omega_arith))
      (by rw [e]; exact VG.Offset.contains_base _ (show j + 1 ≤ 640 by omega_arith) (by omega_arith))
  unfold padded
  refine WP.seq ?_
  simp only [padStart, mr]
  refine wp_li (by decide) fun s₁ u₁ => ?_
  refine wp_std (a := B + BitVec.ofNat 64 padOff) (by decide) (by decide) (by rw [u₁.other _ (by decide), h5])
    (by rw [u₁.wr]; exact scr_in hW (by decide)) fun s₂ u₂ => ?_
  refine wp_addi (by decide) (by decide) fun s₃ u₃ => wp_addi (by decide) (by decide) fun s₄ u₄ =>
    wp_mr fun s₅ u₅ => wp_nil ?_
  obtain m₅ : s₅.mem = t.mem.writeW (B + BitVec.ofNat 64 520) (0 : BitVec 64) := by
    rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.gpr, u₁.mem]; rfl
  obtain g₅ : ∀ r, r ≠ .r0 → r ≠ .r10 → r ≠ .r11 → r ≠ .r12 → s₅.gpr r = t.gpr r := fun r h0 h10 h11 h12 => by
    rw [u₅.other r h12, u₄.other r h11, u₃.other r h10, u₂.gpr, u₁.other r h0]
  obtain wr₅ : s₅.wr = t.wr := by rw [u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]
  obtain rd₅ : s₅.rd = t.rd := by rw [u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd]
  refine WP.seq (copyLoop_wp (src := S + BitVec.ofNat 64 408) (dst := B + BitVec.ofNat 64 520) (n := h)
    (by omega_arith) (by rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, u₂.gpr, u₁.other _ (by decide), h3])
    (by rw [u₅.other _ (by decide), u₄.gpr, u₃.other _ (by decide), u₂.gpr, u₁.other _ (by decide), h5, padOff])
    (by rw [u₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr, u₁.other _ (by decide), h8])
    (fun i hi => by
      rw [rd₅, wr₅, VG.Offset.add_add]
      exact ⟨_, List.mem_append_right _ hS, VG.Offset.contains_base _ (show 408 + i + 1 ≤ 416 by omega_arith) (by omega_arith)⟩)
    (fun i hi => by
      rw [wr₅, VG.Offset.add_add]
      exact ⟨_, hW, VG.Offset.contains_base _ (show 520 + i + 1 ≤ 640 by omega_arith) (by omega_arith)⟩)
    (fun i hi i' hi' => by rw [VG.Offset.add_add, VG.Offset.add_add]; exact sep1 _ _ (by omega_arith) (by omega_arith))
    fun c hc => ?_)
  obtain c3 : c.gpr .r3 = S := by rw [hc.regs _ (by decide) (by decide) (by decide) (by decide), g₅ _ (by decide)
    (by decide) (by decide) (by decide), h3]
  obtain c5 : c.gpr .r5 = B := by rw [hc.regs _ (by decide) (by decide) (by decide) (by decide), g₅ _ (by decide)
    (by decide) (by decide) (by decide), h5]
  obtain cwr : c.wr = t.wr := by rw [hc.wr, wr₅]
  obtain crd : c.rd = t.rd := by rw [hc.rd, rd₅]
  -- The memory but the working space is unchanged.
  obtain fc : Frame [⟨B, 528⟩] t.mem c.mem := by
    intro x hx
    rw [hc.rest x fun i hi e => hx _ List.mem_cons_self (by
        rw [e, VG.Offset.add_add]; exact VG.Offset.contains_base _ (show 520 + i + 1 ≤ 528 by omega_arith) (by omega_arith)), m₅]
    exact ((Frame.refl [(⟨B, 528⟩ : Region)] t.mem).writeW List.mem_cons_self (0 : BitVec 64)
      (VG.Offset.contains_base _ (show 520 + 64 / 8 ≤ 528 by decide) (by decide))) x hx
  simp only [padDone]
  refine wp_li (by decide) fun c₁ u₁ => ?_
  refine wp_stb (a := B + BitVec.ofNat 64 520 + BitVec.ofNat 64 h) (by decide) (by decide)
    (by rw [u₁.other _ (by decide), hc.r11]; exact BitVec.add_zero _)
    (by rw [u₁.wr, cwr, VG.Offset.add_add]
        exact ⟨_, hW, VG.Offset.contains_base _ (show 520 + h + 1 ≤ 640 by omega_arith) (by omega_arith)⟩) fun c₂ u₂ => ?_
  obtain m₂ : c₂.mem = c.mem.writeW (B + BitVec.ofNat 64 520 + BitVec.ofNat 64 h) ((BitVec.ofNat 64 0x80).setWidth 8) := by
    rw [u₂.mem, u₁.gpr, u₁.mem]
  obtain f₂ : Frame [⟨B, 528⟩] t.mem c₂.mem := by
    rw [m₂, VG.Offset.add_add]
    exact fc.writeW List.mem_cons_self _ (VG.Offset.contains_base _ (show 520 + h + 8 / 8 ≤ 528 by omega_arith) (by omega_arith))
  obtain rdS : ∀ off, off + 8 ≤ 416 → c₂.mem.readW (S + BitVec.ofNat 64 off) 64 = t.mem.readW (S + BitVec.ofNat 64 off) 64 :=
    fun off h => f₂.readW (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (hd.sub_right (Region.sub_prefix (by decide))).sub_left (VG.Offset.sub_base _ h)) (by decide)
  obtain hrd₂ : ∀ off, off + 8 ≤ 416 → InRegions (c₂.rd ++ c₂.wr) (S + BitVec.ofNat 64 off) 8 := fun off h => by
    rw [u₂.rd, u₂.wr, u₁.rd, u₁.wr, crd, cwr]; exact inS off h
  refine wp_ld (a := B + BitVec.ofNat 64 padOff) (by decide) (by decide)
    (by rw [u₂.gpr, u₁.other _ (by decide), c5])
    (by rw [u₂.rd, u₂.wr, u₁.rd, u₁.wr, crd, cwr]; exact scr_rd hW (by decide)) fun c₃ u₃ => ?_
  refine wp_ld (a := S + BitVec.ofNat 64 392) (by decide) (by decide)
    (by rw [u₃.other _ (by decide), u₂.gpr, u₁.other _ (by decide), c3])
    (by rw [u₃.rd, u₃.wr]; exact hrd₂ 392 (by decide)) fun c₄ u₄ => wp_xor fun c₅ u₅ => ?_
  refine wp_ld (a := S + BitVec.ofNat 64 400) (by decide) (by decide)
    (by rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr, u₁.other _ (by decide), c3])
    (by rw [u₅.rd, u₅.wr, u₄.rd, u₄.wr, u₃.rd, u₃.wr]; exact hrd₂ 400 (by decide)) fun c₆ u₆ => wp_xor fun c₇ u₇ => ?_
  refine wp_std (a := B + BitVec.ofNat 64 512) (by decide) (by decide)
    (by rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
      u₃.other _ (by decide), u₂.gpr, u₁.other _ (by decide), c5]; rfl)
    (by rw [u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr, cwr]; exact scr_in hW (by decide)) fun c₈ u₈ => wp_nil ?_
  obtain m₇ : c₇.mem = c₂.mem := by rw [u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem]
  obtain a5 : c₅.gpr .r7 = c₂.mem.readW (B + BitVec.ofNat 64 padOff) 64 ^^^ c₂.mem.readW (S + BitVec.ofNat 64 392) 64 := by
    rw [u₅.gpr, u₄.other _ (by decide), u₃.gpr, u₄.gpr, u₃.mem]
  obtain w : c₇.gpr .r7 = c₂.mem.readW (B + BitVec.ofNat 64 padOff) 64 ^^^ c₂.mem.readW (S + BitVec.ofNat 64 392) 64 ^^^
      c₂.mem.readW (S + BitVec.ofNat 64 400) 64 := by
    rw [u₇.gpr, u₆.other _ (by decide), a5, u₆.gpr, u₅.mem, u₄.mem, u₃.mem]
  obtain pad : Spec.Aes.bytesAt c₂.mem (B + BitVec.ofNat 64 padOff) 8 =
      Spec.Aes.bytesAt t.mem (S + BitVec.ofNat 64 408) h ++ [0x80] ++
        Spec.Cmac.zeros (8 - (Spec.Aes.bytesAt t.mem (S + BitVec.ofNat 64 408) h).length - 1) := by
    rw [m₂]
    refine pad_bytes hh (fun i hi => ?_) (fun x hx => ?_) (fun i hi => ?_)
    · rw [hc.copied i hi, m₅, VG.Offset.add_add]
    · rw [hc.rest x hx, m₅]
    · exact ((Frame.refl [(⟨B + BitVec.ofNat 64 520, 8⟩ : Region)] t.mem).writeW List.mem_cons_self (0 : BitVec 64)
        (Region.contains_self _ _)) _ fun r hr hcon => by
          simp only [List.mem_singleton] at hr; subst hr
          exact hd _ (VG.Offset.contains_base _ (show 408 + i + 1 ≤ 416 by omega_arith) (by omega_arith))
            ((VG.Offset.sub_base B (show 520 + 8 ≤ 640 by decide)) _ hcon)
  obtain hlen : (Spec.Aes.bytesAt t.mem (S + BitVec.ofNat 64 408) h).length ≠ 8 := by
    simp [Spec.Aes.bytesAt]; omega_arith
  refine ⟨?_, ?_, fun r h0 h7 h9 h10 h11 h12 => ?_, ?_, ?_⟩
  · rw [u₈.mem, m₇, ← Proof.Cmac.le8_readW, Mem.readW_writeW_self64, w, rdS 392 (by decide), rdS 400 (by decide),
      le8_xor3, Proof.Cmac.le8_readW, Proof.Cmac.le8_readW, Proof.Cmac.le8_readW, pad, finBlock,
      Spec.Cmac.lastBlock, ite_eq_right hlen]
  · rw [u₈.mem, m₇]
    exact f₂.writeW List.mem_cons_self _ (VG.Offset.contains_base _ (show 512 + 64 / 8 ≤ 528 by decide) (by decide))
  · rw [u₈.gpr, u₇.other r h7, u₆.other r h9, u₅.other r h7, u₄.other r h9, u₃.other r h7, u₂.gpr,
      u₁.other r h9, hc.regs r h0 h10 h11 h12, g₅ r h0 h10 h11 h12]
  · rw [u₈.rd, u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd, crd]
  · rw [u₈.wr, u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr, cwr]

/-- `finBlock` reads only the state. -/
theorem finBlock_frame {m m' : Mem} {S B : Addr} {h : Nat} (hh : h ≤ 8) (hf : Frame [⟨B, 640⟩] m m')
    (hd : Region.Disjoint ⟨S, 416⟩ ⟨B, 640⟩) : finBlock m' S h = finBlock m S h := by
  obtain e : ∀ off n, off + n ≤ 416 → Spec.Aes.bytesAt m' (S + BitVec.ofNat 64 off) n =
      Spec.Aes.bytesAt m (S + BitVec.ofNat 64 off) n := fun off n hn =>
    List.map_congr_left fun i hi => hf.bytes (R := ⟨S + BitVec.ofNat 64 off, n⟩) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hd.sub_left (VG.Offset.sub_base _ hn))
      (by show n ≤ 2 ^ 64; omega_arith) (List.mem_range.mp hi)
  rw [finBlock, finBlock, e 400 8 (by decide), e 384 8 (by decide), e 392 8 (by decide), e 408 h (by omega_arith)]

theorem finishSave_wp {s : State} (hp : FinishPre s) {is : List Instr} {Q : State → Prop}
    (k : ∀ t, t.gpr .r31 = s.gpr .r5 → t.gpr .r5 = s.gpr .r6 →
      (∀ r, r ≠ .r0 → r ≠ .r5 → r ≠ .r31 → t.gpr r = s.gpr r) → t.rd = s.rd → t.wr = s.wr →
      t.mem = (s.mem.writeW (s.gpr .r6 + BitVec.ofNat 64 lrOff) s.lr).writeW (s.gpr .r6 + BitVec.ofNat 64 r31Off)
        (s.gpr .r31) → WP isa (.block is) t Q) :
    WP isa (.block (finishSave ++ is)) s Q := by
  obtain hW : (⟨s.gpr .r6, 640⟩ : Region) ∈ s.wr := by rw [hp.wr]; simp
  simp only [finishSave, mr, List.cons_append, List.nil_append]
  refine wp_mflr fun s₁ u₁ => ?_
  refine wp_std (a := s.gpr .r6 + BitVec.ofNat 64 lrOff) (by decide) (by decide) (by rw [u₁.other _ (by decide)])
    (by rw [u₁.wr]; exact scr_in hW (by decide)) fun s₂ u₂ => ?_
  refine wp_std (a := s.gpr .r6 + BitVec.ofNat 64 r31Off) (by decide) (by decide)
    (by rw [u₂.gpr, u₁.other _ (by decide)]) (by rw [u₂.wr, u₁.wr]; exact scr_in hW (by decide)) fun s₃ u₃ => ?_
  refine wp_mr fun s₄ u₄ => wp_mr fun s₅ u₅ => ?_
  refine k s₅ ?_ ?_ (fun r h0 h5 h31 => ?_) (by rw [u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd])
    (by rw [u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]) ?_
  · rw [u₅.other _ (by decide), u₄.gpr, u₃.gpr, u₂.gpr, u₁.other _ (by decide)]
  · rw [u₅.gpr, u₄.other _ (by decide), u₃.gpr, u₂.gpr, u₁.other _ (by decide)]
  · rw [u₅.other r h5, u₄.other r h31, u₃.gpr, u₂.gpr, u₁.other r h0]
  · rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₂.gpr, u₁.gpr, u₁.mem, u₁.other _ (by decide)]

theorem ofNat_sub8_eq_zero {h : Nat} (hh : h ≤ 8) :
    (BitVec.ofNat 64 h - BitVec.ofNat 64 8 == 0) = decide (h = 8) := by
  by_cases e : h = 8
  · subst e; rfl
  · rw [decide_eq_false e]
    simp only [beq_eq_false_iff_ne, ne_eq]
    intro h'
    have := congrArg BitVec.toNat h'
    rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat] at this
    simp at this
    omega_arith

theorem finish_wp (s : State) (hp : FinishPre s) :
    WP isa finish s fun f => (∀ r ∈ preserved, f.gpr r = s.gpr r) ∧ f.lr = s.lr ∧
      Spec.Aes.bytesAt f.mem (s.gpr .r5) 8 = Spec.Cmac.tdesWith (Spec.TripleDes.scheduleAt s.mem (s.gpr .r3))
        (finBlock s.mem (s.gpr .r3) (held (s.gpr .r4).toNat)) := by
  obtain hS : (⟨s.gpr .r3, 416⟩ : Region) ∈ s.wr := by rw [hp.wr]; simp
  obtain hO : (⟨s.gpr .r5, 8⟩ : Region) ∈ s.wr := by rw [hp.wr]; simp
  obtain hW : (⟨s.gpr .r6, 640⟩ : Region) ∈ s.wr := by rw [hp.wr]; simp
  have hfitB := hp.scrFit
  obtain hh := Proof.CmacTripleDes.Stream.held_le (s.gpr .r4).toNat
  obtain cB : ∀ off, off + 8 ≤ 640 → (⟨s.gpr .r6, 640⟩ : Region).Contains (s.gpr .r6 + BitVec.ofNat 64 off) (64 / 8) :=
    fun off h => VG.Offset.contains_base _ h (by omega_arith)
  unfold finish
  refine WP.seq ?_
  rw [← List.append_nil finishSave]
  refine finishSave_wp hp fun t t31 t5 tg trd twr tm => wp_nil ?_
  obtain F0 : Frame [⟨s.gpr .r6, 640⟩] s.mem t.mem := by
    rw [tm]
    exact ((Frame.refl _ _).writeW List.mem_cons_self _ (cB lrOff (by decide))).writeW List.mem_cons_self _
      (cB r31Off (by decide))
  refine WP.seq (heldCode_wp (s.gpr .r4).isLt (by rw [tg _ (by decide) (by decide) (by decide),
    BitVec.ofNat_toNat, BitVec.setWidth_eq]) fun t₁ h8 g₁ m₁ rd₁ wr₁ => ?_)
  refine WP.seq (wp_subi (by decide) (by decide) fun t₂ u₂ => wp_nil (Q := fun t₂ =>
      WP isa (.seq (.ite (.zero .d .r9) (.block complete) padded) (.seq (.block [.addi .r4 .r5 bufOff])
        (.seq encCall (.block finishOut)))) t₂ _) ?_)
  obtain r3₂ : t₂.gpr .r3 = s.gpr .r3 := by rw [u₂.other _ (by decide), g₁ _ (by decide) (by decide),
    tg _ (by decide) (by decide) (by decide)]
  obtain r5₂ : t₂.gpr .r5 = s.gpr .r6 := by rw [u₂.other _ (by decide), g₁ _ (by decide) (by decide), t5]
  obtain r8₂ : t₂.gpr .r8 = BitVec.ofNat 64 (held (s.gpr .r4).toNat) := by rw [u₂.other _ (by decide), h8]
  obtain wr₂ : t₂.wr = s.wr := by rw [u₂.wr, wr₁, twr]
  obtain rd₂ : t₂.rd = s.rd := by rw [u₂.rd, rd₁, trd]
  obtain m₂ : t₂.mem = t.mem := by rw [u₂.mem, m₁]
  -- The branch, to the block in the buffer.
  obtain hb : WP isa (.ite (.zero .d .r9) (.block complete) padded) t₂
      (fun u => BufReady t₂ u (s.gpr .r3) (s.gpr .r6) (held (s.gpr .r4).toNat)) := by
    obtain ev : isa.eval (.zero .d .r9) t₂ = some (decide (held (s.gpr .r4).toNat = 8)) := by
      rw [eval_zero, u₂.gpr, h8, ofNat_sub8_eq_zero hh]
    by_cases e8 : held (s.gpr .r4).toNat = 8
    · refine WP.ite true (by rw [ev, decide_eq_true e8]) (fun _ => ?_) (fun h => by cases h)
      rw [e8]
      exact complete_wp r3₂ r5₂ (by rw [wr₂]; exact hS) (by rw [wr₂]; exact hW)
    · refine WP.ite false (by rw [ev, decide_eq_false e8]) (fun h => by cases h) fun _ => ?_
      exact padded_wp (by omega_arith) r3₂ r5₂ r8₂ (by rw [wr₂]; exact hS) (by rw [wr₂]; exact hW) hp.stateScr
  refine WP.seq (WP.mono hb fun u hu => ?_)
  obtain wru : u.wr = s.wr := by rw [hu.wr, wr₂]
  obtain rdu : u.rd = s.rd := by rw [hu.rd, rd₂]
  obtain ug : ∀ r, r ≠ .r0 → r ≠ .r4 → r ≠ .r7 → r ≠ .r8 → r ≠ .r9 → r ≠ .r10 → r ≠ .r11 → r ≠ .r12 →
      u.gpr r = t.gpr r := fun r h0 h4 h7 h8 h9 h10 h11 h12 => by
    rw [hu.regs r h0 h7 h9 h10 h11 h12, u₂.other r h9, g₁ r h8 h9]
  refine WP.seq (wp_addi (n := .r5) (by decide) (by decide) fun u₁ v₁ => wp_nil ?_)
  obtain u3 : u₁.gpr .r3 = s.gpr .r3 := by
    rw [v₁.other _ (by decide), ug _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide), tg _ (by decide) (by decide) (by decide)]
  obtain u5 : u₁.gpr .r5 = s.gpr .r6 := by
    rw [v₁.other _ (by decide), ug _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide), t5]
  refine WP.seq (encCall_wp u3 (by rw [v₁.gpr, ← u5, v₁.other _ (by decide)]; rfl) u5
    ⟨_, List.mem_append_right _ (by rw [v₁.wr, wru]; exact hS), VG.Offset.contains_base _ (show 0 + 384 ≤ 416 by decide)
      (by decide) |> fun h => by simpa using h⟩ (by rw [v₁.wr, wru]; exact hW) (Nat.le_refl _)
    (hp.stateScr.sub_left (Region.sub_prefix (by decide))) fun v rdv wrv cv v3 v4 v5 fv outv => ?_)
  obtain wrv' : v.wr = s.wr := by rw [wrv, v₁.wr, wru]
  obtain rdv' : v.rd = s.rd := by rw [rdv, v₁.rd, rdu]
  obtain v31 : v.gpr .r31 = s.gpr .r5 := by
    rw [cv _ (by decide), v₁.other _ (by decide), ug _ (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide), t31]
  simp only [finishOut]
  refine wp_ld (a := s.gpr .r6 + BitVec.ofNat 64 bufOff) (by decide) (by decide) (by rw [v5])
    (by rw [rdv', wrv']; exact scr_rd hW (by decide)) fun w₁ x₁ => ?_
  refine wp_std (a := s.gpr .r5) (by decide) (by decide)
    (by rw [x₁.other _ (by decide), v31]; exact BitVec.add_zero _)
    (by rw [x₁.wr, wrv']; exact ⟨_, hO, Region.contains_self _ _⟩) fun w₂ x₂ => ?_
  obtain hR : ∀ off, off + 8 ≤ 640 → InRegions (w₂.rd ++ w₂.wr) (s.gpr .r6 + BitVec.ofNat 64 off) 8 := fun off h => by
    rw [x₂.rd, x₂.wr, x₁.rd, x₁.wr, rdv', wrv']; exact scr_rd hW h
  refine wp_ld (a := s.gpr .r6 + BitVec.ofNat 64 lrOff) (by decide) (by decide)
    (by rw [x₂.gpr, x₁.other _ (by decide), v5]) (hR lrOff (by decide)) fun w₃ x₃ => ?_
  refine wp_ld (a := s.gpr .r6 + BitVec.ofNat 64 r31Off) (by decide) (by decide)
    (by rw [x₃.other _ (by decide), x₂.gpr, x₁.other _ (by decide), v5])
    (by rw [x₃.rd, x₃.wr]; exact hR r31Off (by decide)) fun w₄ x₄ => wp_mtlr (wp_nil ?_)
  -- The memory.
  obtain mw₂ : w₂.mem = v.mem.writeW (s.gpr .r5) (v.mem.readW (s.gpr .r6 + BitVec.ofNat 64 bufOff) 64) := by
    rw [x₂.mem, x₁.gpr, x₁.mem]
  obtain Fu : Frame [⟨s.gpr .r6, 640⟩] s.mem u.mem := F0.trans (by
    rw [← m₂]; exact hu.frame.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_singleton_self _, Region.sub_prefix (by decide)⟩)
  -- The saved slots, through the branch, the call and the output.
  obtain slot : ∀ off, 528 ≤ off → off + 8 ≤ 640 → w₂.mem.readW (s.gpr .r6 + BitVec.ofNat 64 off) 64 =
      t.mem.readW (s.gpr .r6 + BitVec.ofNat 64 off) 64 := fun off h1 h2 => by
    rw [mw₂, readW_sep64 ((hp.outScr.sub_right (VG.Offset.sub_base _ h2)).symm),
      fv.readW (Region.contains_self _ _) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact VG.Offset.disjoint_base _ (by omega_arith) (by omega_arith)) (by decide), v₁.mem,
      hu.frame.readW (Region.contains_self _ _) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact VG.Offset.disjoint_base _ (by omega_arith) (by omega_arith)) (by decide), m₂]
  refine ⟨fun r hr => ?_, ?_, ?_⟩
  · by_cases e31 : r = .r31
    · subst e31
      show w₄.gpr .r31 = _
      rw [x₄.gpr, x₃.mem, slot r31Off (by decide) (by decide), tm, Mem.readW_writeW_self64]
    obtain ⟨h0, h3', h4', h5', h6', h7', h8', h9', h10', h11', h12'⟩ := preserved_ne r hr
    show w₄.gpr r = _
    rw [x₄.other r e31, x₃.other r h0, x₂.gpr, x₁.other r h7', cv r hr, v₁.other r h4',
      ug r h0 h4' h7' h8' h9' h10' h11' h12', tg r h0 h5' e31]
  · show w₄.gpr .r0 = _
    rw [x₄.other _ (by decide), x₃.gpr, slot lrOff (by decide) (by decide), tm,
      readW_sep64 (VG.Offset.disjoint _ (by decide) (by decide) (by decide)), Mem.readW_writeW_self64]
  · show Spec.Aes.bytesAt w₄.mem (s.gpr .r5) 8 = _
    rw [x₄.mem, x₃.mem, mw₂, ← Proof.Cmac.le8_readW, Mem.readW_writeW_self64, Proof.Cmac.le8_readW, bufOff,
      VG.Proof.TripleDes.bytesAt_eq, outv, v₁.mem, Proof.TripleDes.scheduleAt_eq_of_frame _ Fu (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact hp.stateScr.sub_left (Region.sub_prefix (by decide))),
      ← VG.Proof.TripleDes.ofFn_bytesAt, hu.buf, m₂, finBlock_frame hh F0 hp.stateScr]
    rfl

/-- The block `finish` enciphers, for a state that represents `msg`: its
cipher is the MAC. -/
theorem finish_spec {m : Mem} {S : Addr} {key msg : List Byte} (hr : Spec.Cmac.tdesRepr m S key msg) :
    Spec.Cmac.tdesWith (Spec.TripleDes.scheduleAt m S) (finBlock m S (held msg.length)) =
      Spec.Cmac.tdesCmac key 8 msg := by
  obtain ⟨hm, hne, hc, hcat⟩ := Proof.CmacTripleDes.Stream.repr_finish hr
  obtain ⟨-, hs, hk, -, -⟩ := hr
  obtain hks : Spec.Aes.bytesAt m (S + BitVec.ofNat 64 384) 8 = (Spec.Cmac.subkeys (Spec.Cmac.tdes key) 8).1 ∧
      Spec.Aes.bytesAt m (S + BitVec.ofNat 64 392) 8 = (Spec.Cmac.subkeys (Spec.Cmac.tdes key) 8).2 := by
    obtain hl1 : (Spec.Cmac.subkeys (Spec.Cmac.tdes key) 8).1.length = 8 := by
      rw [Spec.Cmac.tdes, Proof.CmacTripleDes.subkeys_tdes]; exact Proof.Cmac.length_le8 _
    have e := hk
    rw [show (S + 384 : Addr) = S + BitVec.ofNat 64 384 from rfl, Proof.Cmac.bytesAt_split, VG.Offset.add_add,
      show (384 + 8 : Nat) = 392 from rfl] at e
    exact List.append_inj e (by simp [Spec.Aes.bytesAt, hl1])
  obtain hl := Proof.CmacTripleDes.Stream.held_le msg.length
  rw [Proof.CmacTripleDes.Stream.tdesCmac_eq]
  conv => rhs; rw [← hcat]
  rw [Proof.CmacTripleDes.macFull_split8 _ hm (by simp [Spec.Aes.bytesAt]; omega_arith) (by
      rcases hne with h | h
      · exact .inl h
      · exact .inr (by simp [Spec.Aes.bytesAt]; omega_arith)),
    ← hc, ← hks.1, ← hks.2, hs]
  rfl

end VG.Proof.CmacTripleDes.Stream.PPC64LE

end

end


/-!
# Streaming TDEA-CMAC on PPC64LE: `Verified`

The contracts the proofs are written against (`initPPC`, `absorbPPC`,
`finishPPC`), with the working space as the last argument, which the shared
contracts with the working space as an argument
(`Proof/CmacTripleDes/StreamScratch.lean`) imply, with no stack: the
functions and the functions they call keep the return address in the link
register.
-/

@[expose] public section

namespace VG.Proof.CmacTripleDes.Stream.PPC64LE

open VG VG.PPC64LE VG.Impl.CmacTripleDes.Stream.PPC64LE

/-- `vg_cmac_triple_des_stream_init(state = r3, key = r4, key_len = r5, scratch = r6)`. -/
def initPPC : Contract isa where
  pre s :=
    let state : Region := ⟨s.gpr .r3, 416⟩
    let key : Region := ⟨s.gpr .r4, (s.gpr .r5).toNat⟩
    let scr : Region := ⟨s.gpr .r6, 640⟩
    s.rd = [key] ∧ s.wr = [state, scr] ∧ state.Disjoint key ∧ state.Disjoint scr ∧ key.Disjoint scr ∧
      (s.gpr .r3).toNat + 416 ≤ 2 ^ 64 ∧ (s.gpr .r4).toNat + (s.gpr .r5).toNat ≤ 2 ^ 64 ∧
      (s.gpr .r6).toNat + 640 ≤ 2 ^ 64 ∧ Spec.TripleDes.validKey (s.gpr .r5).toNat
  post s s' :=
    Spec.Cmac.tdesRepr s'.mem (s.gpr .r3) (Spec.TripleDes.bytesAt s.mem (s.gpr .r4) (s.gpr .r5).toNat) []
  pub := pub4

/-- `vg_cmac_triple_des_absorb(state = r3, count = r4, data = r5, len = r6, scratch = r7)`. -/
def absorbPPC : Contract isa where
  pre s :=
    let state : Region := ⟨s.gpr .r3, 416⟩
    let data : Region := ⟨s.gpr .r5, (s.gpr .r6).toNat⟩
    let scr : Region := ⟨s.gpr .r7, 688⟩
    s.rd = [data] ∧ s.wr = [state, scr] ∧
      state.Disjoint data ∧ state.Disjoint scr ∧ data.Disjoint scr ∧
      (s.gpr .r3).toNat + 416 ≤ 2 ^ 64 ∧ (s.gpr .r5).toNat + (s.gpr .r6).toNat ≤ 2 ^ 64 ∧
      (s.gpr .r7).toNat + 688 ≤ 2 ^ 64
  post s s' :=
    ∀ key msg, Spec.Cmac.tdesRepr s.mem (s.gpr .r3) key msg →
      s.gpr .r4 = BitVec.ofNat 64 msg.length → msg.length + (s.gpr .r6).toNat < 2 ^ 64 →
      Spec.Cmac.tdesRepr s'.mem (s.gpr .r3) key
        (msg ++ Spec.Aes.bytesAt s.mem (s.gpr .r5) (s.gpr .r6).toNat)
  pub := pub5

/-- `vg_cmac_triple_des_finish(state = r3, count = r4, out = r5, scratch = r6)`. -/
def finishPPC : Contract isa where
  pre s :=
    let state : Region := ⟨s.gpr .r3, 416⟩
    let out : Region := ⟨s.gpr .r5, 8⟩
    let scr : Region := ⟨s.gpr .r6, 640⟩
    s.rd = [] ∧ s.wr = [state, out, scr] ∧
      state.Disjoint out ∧ state.Disjoint scr ∧ out.Disjoint scr ∧
      (s.gpr .r3).toNat + 416 ≤ 2 ^ 64 ∧ (s.gpr .r5).toNat + 8 ≤ 2 ^ 64 ∧
      (s.gpr .r6).toNat + 640 ≤ 2 ^ 64
  post s s' :=
    ∀ key msg, Spec.Cmac.tdesRepr s.mem (s.gpr .r3) key msg →
      s.gpr .r4 = BitVec.ofNat 64 msg.length → msg.length < 2 ^ 64 →
      Spec.Aes.bytesAt s'.mem (s.gpr .r5) 8 = Spec.Cmac.tdesCmac key 8 msg
  pub := pub4

theorem pub4_iff (s₁ s₂ : State) : pub4 s₁ s₂ ↔ s₁.sp = s₂.sp ∧ s₁.gpr .r3 = s₂.gpr .r3 ∧
    s₁.gpr .r4 = s₂.gpr .r4 ∧ s₁.gpr .r5 = s₂.gpr .r5 ∧ s₁.gpr .r6 = s₂.gpr .r6 := by
  simp [Proof.TripleDes.PPC64LE.PublicRegs]

theorem pub5_iff (s₁ s₂ : State) : pub5 s₁ s₂ ↔ s₁.sp = s₂.sp ∧ s₁.gpr .r3 = s₂.gpr .r3 ∧
    s₁.gpr .r4 = s₂.gpr .r4 ∧ s₁.gpr .r5 = s₂.gpr .r5 ∧ s₁.gpr .r6 = s₂.gpr .r6 ∧ s₁.gpr .r7 = s₂.gpr .r7 := by
  simp [Proof.TripleDes.PPC64LE.PublicRegs]

/-- `count` is the message's length. -/
theorem count_eq {c : BitVec 64} {n : Nat} (h : c = BitVec.ofNat 64 n) (hn : n < 2 ^ 64) : c.toNat = n := by
  rw [h, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn]

/-! ## Correctness -/

theorem init_correct (s : State) (hs : initPPC.pre s) :
    ∃ t s', Exec isa streamInit s t s' ∧ abiPreserved s s' ∧ initPPC.post s s' := by
  obtain ⟨hrd, hwr, dSK, dSW, dKW, fS, -, fW, hv⟩ := hs
  obtain ⟨t, s', he, h1, h2, h3⟩ := init_wp s ⟨hrd, hwr, dSK.symm, dKW, dSW, hv, fS, fW⟩
  exact ⟨t, s', he, ⟨h1, Exec.sp he, h2⟩, h3⟩

theorem absorb_correct (s : State) (hs : absorbPPC.pre s) :
    ∃ t s', Exec isa absorb s t s' ∧ abiPreserved s s' ∧ absorbPPC.post s s' := by
  obtain ⟨hrd, hwr, dSD, dSW, dDW, fS, fD, fW⟩ := hs
  obtain ⟨t, s', he, h1, h2, h3⟩ := absorb_wp s ⟨hrd, hwr, dSD.symm, dDW, dSW, fS, fD, fW⟩
  exact ⟨t, s', he, ⟨h1, Exec.sp he, h2⟩, fun key msg hr hc hl => h3 key msg hr (count_eq hc (by omega_using [hl])).symm⟩

theorem finish_correct (s : State) (hs : finishPPC.pre s) :
    ∃ t s', Exec isa finish s t s' ∧ abiPreserved s s' ∧ finishPPC.post s s' := by
  obtain ⟨hwr, dSO, dSW, dOW, fS, fO, fW⟩ := hs.2
  obtain ⟨t, s', he, h1, h2, h3⟩ := finish_wp s ⟨hwr, dSO, dSW, dOW, fS, fO, fW⟩
  refine ⟨t, s', he, ⟨h1, Exec.sp he, h2⟩, fun key msg hr hc hl => ?_⟩
  rw [h3, count_eq hc hl, finish_spec hr]

/-! ## The contracts -/

/-- A state satisfying `vg_cmac_triple_des_stream_init`'s precondition. -/
def initSat : State where
  gpr r := match r with
    | .r3 => 0x1000 | .r4 => 0x3000 | .r5 => 16 | .r6 => 0x4000 | _ => 0
  lr := 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x3000, 16⟩]
  wr := [⟨0x1000, 416⟩, ⟨0x4000, 640⟩]

theorem init_implies : initPPC.Implies (streamInitScratchContract PPC64LE.abi 0) := by
  sig_implies [streamInitScratchContract, streamInitScratchSig, Spec.Cmac.tdesStreamInitPre,
    Spec.Cmac.tdesStreamInitPost, initPPC, pub4_iff, PPC64LE.abi, PPC64LE.argRegs] [initSat] using initSat

/-- A state satisfying `vg_cmac_triple_des_absorb`'s precondition (with no data). -/
def absorbSat : State where
  gpr r := match r with
    | .r3 => 0x1000 | .r5 => 0x3000 | .r7 => 0x4000 | _ => 0
  lr := 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x3000, 0⟩]
  wr := [⟨0x1000, 416⟩, ⟨0x4000, 688⟩]

theorem absorb_implies : absorbPPC.Implies (absorbScratchContract PPC64LE.abi 0) := by
  sig_implies [absorbScratchContract, absorbScratchSig, Spec.Cmac.tdesAbsorbPost, absorbPPC, pub5_iff,
    PPC64LE.abi, PPC64LE.argRegs] [absorbSat] using absorbSat

/-- A state satisfying `vg_cmac_triple_des_finish`'s precondition. -/
def finishSat : State where
  gpr r := match r with
    | .r3 => 0x1000 | .r5 => 0x2000 | .r6 => 0x4000 | _ => 0
  lr := 0
  sp := 0x8000
  mem _ := 0
  rd := []
  wr := [⟨0x1000, 416⟩, ⟨0x2000, 8⟩, ⟨0x4000, 640⟩]

theorem finish_implies : finishPPC.Implies (finishScratchContract PPC64LE.abi 0) := by
  sig_implies [finishScratchContract, finishScratchSig, Spec.Cmac.tdesFinishPost, finishPPC, pub4_iff,
    PPC64LE.abi, PPC64LE.argRegs] [finishSat] using finishSat

theorem init_verified : Verified PPC64LE.target streamInit (streamInitScratchContract PPC64LE.abi 0) :=
  Verified.of_correct init_correct (init_ct _) init_implies

theorem absorb_verified : Verified PPC64LE.target absorb (absorbScratchContract PPC64LE.abi 0) :=
  Verified.of_correct absorb_correct (absorb_ct _) absorb_implies

theorem finish_verified : Verified PPC64LE.target finish (finishScratchContract PPC64LE.abi 0) :=
  Verified.of_correct finish_correct (finish_ct _) finish_implies

end VG.Proof.CmacTripleDes.Stream.PPC64LE

end

end


/-!
# Streaming TDEA-CMAC on PPC64LE, with its working space on the stack

The streaming functions run their code, proved with the working space as an
argument (`Verified.lean`), in a frame that allocates it
(`Verified.stackScratch`): the frame's 32-byte header and 640 bytes, 688 for
`absorb`. Their code uses no other stack: it and the functions it calls keep
the return address in the link register.
-/

@[expose] public section

namespace VG.Proof.CmacTripleDes.Stream.PPC64LE

open VG VG.PPC64LE VG.Impl.CmacTripleDes.Stream.PPC64LE

/-- A state satisfying `vg_cmac_triple_des_stream_init`'s precondition,
without the working space. -/
def initFrameSat : State := { initSat with wr := [⟨0x1000, 416⟩] }

theorem initFrameSat_pre : ∃ s, (Spec.Cmac.tdesStreamInitContract PPC64LE.abi (0 + 672)).pre s := by
  implies_sat [Spec.Cmac.tdesStreamInitContract, Spec.Cmac.tdesStreamInitSig, Spec.Cmac.tdesStreamInitPre,
    Spec.Cmac.tdesStreamInitPost, PPC64LE.abi, PPC64LE.argRegs] [initFrameSat, initSat] using initFrameSat

/-- A state satisfying `vg_cmac_triple_des_absorb`'s precondition, without
the working space (and with no data). -/
def absorbFrameSat : State := { absorbSat with wr := [⟨0x1000, 416⟩] }

theorem absorbFrameSat_pre : ∃ s, (Spec.Cmac.tdesAbsorbContract PPC64LE.abi (0 + 720)).pre s := by
  implies_sat [Spec.Cmac.tdesAbsorbContract, Spec.Cmac.tdesAbsorbSig, Spec.Cmac.tdesAbsorbPost,
    PPC64LE.abi, PPC64LE.argRegs] [absorbFrameSat, absorbSat] using absorbFrameSat

/-- A state satisfying `vg_cmac_triple_des_finish`'s precondition, without
the working space. -/
def finishFrameSat : State := { finishSat with wr := [⟨0x1000, 416⟩, ⟨0x2000, 8⟩] }

theorem finishFrameSat_pre : ∃ s, (Spec.Cmac.tdesFinishContract PPC64LE.abi (0 + 672)).pre s := by
  implies_sat [Spec.Cmac.tdesFinishContract, Spec.Cmac.tdesFinishSig, Spec.Cmac.tdesFinishPost,
    PPC64LE.abi, PPC64LE.argRegs] [finishFrameSat, finishSat] using finishFrameSat

theorem init_framed :
    Verified PPC64LE.target (Impl.StackScratch.PPC64LE.withStackScratch 672 .r6 streamInit)
      (Spec.Cmac.tdesStreamInitContract PPC64LE.abi 672) :=
  PPC64LE.Verified.stackScratch (sig := Spec.Cmac.tdesStreamInitSig) (nm := "scratch") (e := .u64) (n := 80)
    (pre := Spec.Cmac.tdesStreamInitPre PPC64LE.abi.ptrBits)
    (post := Spec.Cmac.tdesStreamInitPost PPC64LE.abi.ptrBits)
    (wa := false) (stack := 0) (bytes := 672) init_verified (by decide) (by decide)
    (streamInitPre_local _) (streamInitPost_local _)
    (fun vs m m₁ m₂ r hl _ hb h => streamInitPostOut_local _ vs m m₁ m₂ r hl hb h) initFrameSat_pre

theorem absorb_framed :
    Verified PPC64LE.target (Impl.StackScratch.PPC64LE.withStackScratch 720 .r7 absorb)
      (Spec.Cmac.tdesAbsorbContract PPC64LE.abi 720) :=
  PPC64LE.Verified.stackScratch (sig := Spec.Cmac.tdesAbsorbSig) (nm := "scratch") (e := .u64) (n := 86)
    (post := Spec.Cmac.tdesAbsorbPost PPC64LE.abi.ptrBits)
    (wa := false) (stack := 0) (bytes := 720) absorb_verified (by decide) (by decide)
    (fun _ _ _ _ _ _ => by rw [Curry.apply_const]; trivial) (absorbPost_local _)
    (fun vs m m₁ m₂ r hl _ hb h => absorbPostOut_local _ vs m m₁ m₂ r hl hb h) absorbFrameSat_pre

theorem finish_framed :
    Verified PPC64LE.target (Impl.StackScratch.PPC64LE.withStackScratch 672 .r6 finish)
      (Spec.Cmac.tdesFinishContract PPC64LE.abi 672) :=
  PPC64LE.Verified.stackScratch (sig := Spec.Cmac.tdesFinishSig) (nm := "scratch") (e := .u64) (n := 80)
    (post := Spec.Cmac.tdesFinishPost PPC64LE.abi.ptrBits)
    (wa := false) (stack := 0) (bytes := 672) finish_verified (by decide) (by decide)
    (fun _ _ _ _ _ _ => by rw [Curry.apply_const]; trivial) (finishPost_local _)
    (fun vs m m₁ m₂ r hl _ hb h => finishPostOut_local _ vs m m₁ m₂ r hl hb h) finishFrameSat_pre

end VG.Proof.CmacTripleDes.Stream.PPC64LE
