module

public import VerifiedGarbage.Proof.Dsa.PPC64LE.Gen.Test
public import VerifiedGarbage.Spec.Dsa
import VerifiedGarbage.Proof.Dsa.Generation.SeedAdd
import VerifiedGarbage.Proof.Dsa.Generation.Memory
import VerifiedGarbage.Proof.Framework.PPC64LE.ByteStep
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Dsa.Encoding
public import VerifiedGarbage.Proof.Dsa.Generation.PCandidate
import VerifiedGarbage.Proof.Dsa.Digest
import VerifiedGarbage.Proof.Dsa.Arithmetic
import VerifiedGarbage.Proof.Dsa.Generation.PReduction
import VerifiedGarbage.Proof.Dsa.Generation.QShapeMemory
public import VerifiedGarbage.Proof.Ffdh.ParameterCandidate.ShapeOctets
import VerifiedGarbage.Proof.Dsa.Generation.QCandidate
public import VerifiedGarbage.Proof.MdStream.PPC64LE.Common
public import VerifiedGarbage.Proof.Framework.PPC64LE.RelCT
import VerifiedGarbage.Proof.MdStream.PPC64LE.Words
import VerifiedGarbage.Proof.Sha256.Stream

/-! ### `Dsa.PPC64LE.Gen.QPart`, which this module and modules that import it used -/

section

/-! ### `Dsa.PPC64LE.Gen.Hash`, which this module and modules that import it used -/

section

/-! # DSA parameter generation on PPC64LE: a hash of one block

`hash pLen Gh dst` (`Impl/Dsa/PPC64LE/Generation.lean`) hashes the block at
`sMsg`: the initial hash value into `sState` (`ivAt_ok`), the compression
function on it (`MdStream.PPC64LE.compressAt_ok`), and the hash value's words
big-endian at `dst` (`MdStream.PPC64LE.out32_ok`). `HashOk Gh` is what the
proof needs of the hash function: its compression function verified, as the
streaming proofs see it, and its digest of a message of fewer than 56 bytes
as that compression of its one padded block.
-/

@[expose] public section

namespace VG.Proof.Dsa.PPC64LE.Gen
open VG VG.PPC64LE VG.Proof.MdStream VG.Proof.MdStream.PPC64LE
open VG.Impl.Dsa.PPC64LE.Generation

/-! ## The initial hash value -/

/-- `ivStore` from word `n` on. -/
def ivAt (iv : List (BitVec 32)) (n : Nat) : List Instr :=
  (iv.zipIdx n).flatMap fun (v, i) => loadImm .r0 v.toNat ++ [.store .w .r0 .r28 (sState + 4 * i)]

theorem ivStore_eq (iv : List (BitVec 32)) : ivStore iv = ivAt iv 0 := rfl

/-- `lis` and `ori` of a word's halves leave it in the low half. -/
theorem loadImm_lo (v : BitVec 32) :
    ((BitVec.ofNat 16 (v.toNat / 65536) ++ (0 : BitVec 16)).signExtend 64 |||
      (BitVec.ofNat 16 (v.toNat % 65536)).setWidth 64).setWidth 32 = v := by
  obtain e1 : BitVec.ofNat 16 (v.toNat / 65536) = v.extractLsb' 16 16 := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ofNat, BitVec.extractLsb'_toNat]
    rw [show (65536 : Nat) = 2 ^ 16 from rfl, Nat.shiftRight_eq_div_pow]
  obtain e2 : BitVec.ofNat 16 (v.toNat % 65536) = v.extractLsb' 0 16 := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ofNat, BitVec.extractLsb'_toNat, Nat.shiftRight_zero]
    rw [Nat.mod_mod_of_dvd _ (by decide)]
  rw [e1, e2]; exact lis_ori v

/-- `ivAt iv n`: the words of `iv` to `sState + 4 (n + j)`. -/
theorem ivAt_ok {G : GP} : ∀ (iv : List (BitVec 32)) (n : Nat) (s : State) (rest : List Instr) (Q : State → Prop),
    s.gpr .r28 = G.scr → sState + 4 * (n + iv.length) < 2 ^ 15 → G.scr.toNat + sState + 4 * (n + iv.length) ≤ 2 ^ 64 →
    (∀ j < iv.length, InRegions s.wr (G.sa (sState + 4 * (n + j))) 4) →
    (∀ t, Keep [.r0] s t → t.sp = s.sp → Frame [G.rs (sState + 4 * n) (4 * iv.length)] s.mem t.mem →
      (∀ j (hj : j < iv.length), t.mem.readW (G.sa (sState + 4 * (n + j))) 32 = iv[j]) →
      WP isa (.block rest) t Q) →
    WP isa (.block (ivAt iv n ++ rest)) s Q
  | [], _, s, _, _, _, _, _, _, k => k s (Keep.refl _ _) rfl (Frame.refl _ _) fun _ hj => absurd hj (by simp)
  | v :: vs, n, s, rest, Q, h28, hn, hf, hw, k => by
    simp only [List.length_cons] at hn hf hw
    simp only [ivAt, List.zipIdx_cons, List.flatMap_cons, loadImm, List.cons_append, List.nil_append]
    refine WP.wr exec_lis fun s₁ u₁ sp₁ _ => WP.wr exec_ori fun s₂ u₂ sp₂ _ => ?_
    obtain e28 : s₂.gpr .r28 = G.scr := by rw [u₂.other _ (by decide), u₁.other _ (by decide), h28]
    obtain hw0 := hw 0 (by omega_using [])
    rw [Nat.add_zero] at hw0
    refine VG.PPC64LE.WP.cons
      (s' := { s₂ with mem := s₂.mem.writeW (G.sa (sState + 4 * n)) ((s₂.gpr .r0).setWidth 32) }) ?_ ?_
    · rw [exec_store_w (by decide) (by omega_using [hn]) (by rw [e28, u₂.wr, u₁.wr]; exact hw0), e28]
    obtain v₂ : (s₂.gpr .r0).setWidth 32 = v := by rw [u₂.gpr, u₁.gpr]; exact loadImm_lo v
    refine ivAt_ok vs (n + 1) _ rest Q (by exact e28) (by omega_using [hn]) (by omega_using [hf])
      (fun j hj => by
        rw [show n + 1 + j = n + (j + 1) by omega_using []]; show InRegions s₂.wr _ 4
        rw [u₂.wr, u₁.wr]; exact hw (j + 1) (by omega_using [hj]))
      fun t K' sp' F' W' => ?_
    obtain fit1 : G.scr.toNat + (sState + 4 * n + 4) ≤ 2 ^ 64 := by omega_using [hf]
    refine k t ⟨fun r hr => ?_, by rw [K'.2.1]; show s₂.rd = s.rd; rw [u₂.rd, u₁.rd],
      by rw [K'.2.2]; show s₂.wr = s.wr; rw [u₂.wr, u₁.wr]⟩ (by rw [sp']; show s₂.sp = s.sp; rw [sp₂, sp₁]) ?_
      fun j hj => ?_
    · rw [K'.1 r hr]; show s₂.gpr r = s.gpr r
      rw [u₂.other _ (by simpa using hr), u₁.other _ (by simpa using hr)]
    · have f₂ : Frame [G.rs (sState + 4 * n) (4 * (vs.length + 1))] s.mem
          (s₂.mem.writeW (G.sa (sState + 4 * n)) ((s₂.gpr .r0).setWidth 32)) := by
        rw [u₂.mem, u₁.mem]
        exact Frame.writeW (r := G.rs (sState + 4 * n) (4 * (vs.length + 1))) (w := 32) (Frame.refl _ _)
          List.mem_cons_self _ (Offset.contains G.scr (d := sState + 4 * n) (n := 4) (Nat.le_refl _)
            (by omega_using []) (by omega_using [hn]))
      refine Frame.trans f₂ (Frame.sub F' fun r hr => ?_)
      simp only [List.mem_singleton] at hr; subst hr
      refine ⟨_, List.mem_cons_self, Offset.sub _ (by omega_using []) (by simp only [List.length_cons]; omega_using [])⟩
    · cases j with
      | zero =>
        rw [Nat.add_zero]
        rw [F'.readW (r := G.rs (sState + 4 * n) 4) (Region.contains_self _ _) (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact Offset.disjoint _ (.inl (by omega_using [])) (by omega_using [hn]) (by omega_using [hn])) (by decide)]
        show (s₂.mem.writeW (G.sa (sState + 4 * n)) ((s₂.gpr .r0).setWidth 32)).readW _ 32 = _
        rw [Mem.readW_writeW_self32, v₂]; rfl
      | succ j =>
        have := W' j (by simp at hj; omega_using [hj])
        rw [show n + 1 + j = n + (j + 1) by omega_using []] at this
        exact this

/-! ## What the proof needs of the hash function -/

/-- The block of a message of fewer than 56 bytes. -/
def blk {B N L : Nat} (md : MdStream.Md B N L) (msg : List Byte) : List Byte :=
  msg ++ [0x80] ++ List.replicate (55 - msg.length) 0 ++ md.lenBytes msg.length

structure HashOk (Gh : Hash) where
  P : VG.Impl.MdStream.PPC64LE.Params
  md : MdStream.Md P.B P.N P.L
  hB : P.B = 64
  hL : P.L = 8
  hN : P.N = 4 * Gh.k
  hso : P.so ≤ 1024
  hso0 : 0 < P.so
  hk : Gh.k ≤ 8
  hk0 : 0 < Gh.k
  ivLen : Gh.iv.length = Gh.k
  callee : CalleeOk md Gh.code
  ct : ConstantTime isa (compressK md).pre (compressK md).pub Gh.code
  /-- The initial hash value. -/
  H0 : md.HV
  iv : ∀ (m : Mem) (p : Addr), (∀ j (hj : j < Gh.iv.length), m.readW (p + BitVec.ofNat 64 (4 * j)) 32 = Gh.iv[j]) →
    md.stateAt m p = H0
  digest : ∀ (m : Mem) (p : Addr), md.digest (md.stateAt m p) =
    (List.range Gh.k).flatMap fun j => MdStream.bytes32 true (m.readW (p + BitVec.ofNat 64 (4 * j)) 32)
  /-- The hash function. -/
  H : List Byte → List Byte
  hash : ∀ msg, msg.length < 56 → H msg = md.digest (md.compress H0 (md.parse fun t => (blk md msg).getD t 0))
  /-- The taint analysis of the code before and after the call, which
  depends on the hash function only through its initial hash value and its
  words: checked on each instance. -/
  cert1 : ∀ L, ∃ hc, (VG.Taint.check VG.PPC64LE.taint (Taint.ofRegs [.r28])
    (.block (ivStore Gh.iv ++ [scr .r26 sState, scr .r27 (wB L), scr .r4 sMsg])) hc).isSome = true
  cert3 : ∀ dst, ∃ hc, (VG.Taint.check VG.PPC64LE.taint (Taint.ofRegs [.r28, .r26])
    (.block ([.addi .r28 .r28 dst] ++ VG.Impl.MdStream.PPC64LE.out32 Gh.k true ++ [.subi .r28 .r28 dst])) hc).isSome = true

/-! ## The pieces -/

/-- The registers the hash changes before the call. -/
abbrev hRegs : List Reg := [.r0, .r3, .r4, .r5, .r6, .r26, .r27]

/-- The registers the hash changes. -/
abbrev hashRegs : List Reg := .r26 :: .r27 :: volatile

section
variable {G : GP} {STK : Nat} {Gh : Hash} (HO : HashOk Gh)

/-- After the initial hash value and the pointers. -/
abbrev H1 (F : State → State → Prop) (σ s : State) : Prop :=
  ∃ s₀, F σ s₀ ∧ Keep hRegs s₀ s ∧ s.sp = s₀.sp ∧ Frame [G.rs sState (4 * Gh.k)] s₀.mem s.mem ∧
    (∀ j (hj : j < Gh.iv.length), s.mem.readW (G.sa (sState + 4 * j)) 32 = Gh.iv[j]) ∧
    s.gpr .r26 = G.sa sState ∧ s.gpr .r27 = G.sa (wB G.pLen) ∧ s.gpr .r4 = G.sa sMsg

theorem H1.pub {F : State → State → Prop} {c : State → Cfg} (hF : ∀ σ s, F σ s → SS G STK σ (c σ) s) :
    Pub G (H1 (G := G) (Gh := Gh) F) := fun σ s ⟨s₀, h₀, K, sp, _⟩ =>
  ⟨by rw [K.gpr (by decide)]; exact (hF σ s₀ h₀).gi.r28, by rw [sp]; exact (SS.pub hF σ s₀ h₀).2⟩

include HO in
theorem hash1_vp {F : State → State → Prop} {c : State → Cfg} (hF : ∀ σ s, F σ s → SS G STK σ (c σ) s) :
    VP F (.block (ivStore Gh.iv ++ [scr .r26 sState, scr .r27 (wB G.pLen), scr .r4 sMsg]))
      (H1 (G := G) (Gh := Gh) F) := by
  refine VP.pub (SS.pub hF) [] (HO.cert1 G.pLen) (fun _ _ _ _ _ _ _ h => absurd h (by simp)) fun σ s hs => ?_
  obtain h := hF σ s hs
  have gi := h.gi
  have big := gi.wBig
  have fit := gi.scrFit
  have hE := gi.hEnd_le
  have hk := HO.hk
  have il := HO.ivLen
  have lens := gi.lens3
  obtain wBl : wB G.pLen < 2 ^ 15 := by rcases lens with e | e | e <;> rw [e] <;> decide
  obtain wBh : sState + 32 ≤ wB G.pLen := by rcases lens with e | e | e <;> rw [e] <;> decide
  rw [ivStore_eq]
  refine ivAt_ok Gh.iv 0 s _ _ gi.r28 (by simp only [sState] at wBh ⊢; omega_using [hk, il]) (by omega_using [big, fit, hk, il, wBh])
    (fun j hj => gi.inScr (by simp only [sState] at wBh ⊢; omega_using [big, hk, il, wBh, hj])) fun s₁ K₁ sp₁ F₁ W₁ => ?_
  refine WP.wr (exec_addi (by decide) (by decide)) fun s₂ u₂ sp₂ _ => ?_
  refine WP.wr (exec_addi (by decide) wBl) fun s₃ u₃ sp₃ _ => ?_
  refine WP.wr (exec_addi (by decide) (by decide)) fun t u sp _ => WP.block_nil ⟨s, hs, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have r28₁ : s₁.gpr .r28 = s.gpr .r28 := K₁.gpr (by decide)
    refine ⟨fun r hr => ?_, by rw [u.rd, u₃.rd, u₂.rd, K₁.2.1], by rw [u.wr, u₃.wr, u₂.wr, K₁.2.2]⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [u.other _ hr.2.2.1, u₃.other _ hr.2.2.2.2.2.2, u₂.other _ hr.2.2.2.2.2.1, K₁.gpr (by simpa using hr.1)]
  · rw [sp, sp₃, sp₂, sp₁]
  · rw [u.mem, u₃.mem, u₂.mem, ← il]; simpa only [Nat.mul_zero, Nat.add_zero] using F₁
  · intro j hj; rw [u.mem, u₃.mem, u₂.mem]; simpa only [Nat.zero_add] using W₁ j hj
  · rw [u.other _ (by decide), u₃.other _ (by decide), u₂.gpr, K₁.gpr (by decide), gi.r28]
  · rw [u.other _ (by decide), u₃.gpr, u₂.other _ (by decide), K₁.gpr (by decide), gi.r28]
  · rw [u.gpr, u₃.other _ (by decide), u₂.other _ (by decide), K₁.gpr (by decide), gi.r28]

/-- With the compression function's arguments. -/
abbrev H1c (F : State → State → Prop) (σ s : State) : Prop :=
  H1 (G := G) (Gh := Gh) F σ s ∧ s.gpr .r3 = G.sa sState ∧ s.gpr .r5 = 1 ∧ s.gpr .r6 = G.sa (wB G.pLen)

theorem hash2a_vp {F : State → State → Prop} {c : State → Cfg} (hF : ∀ σ s, F σ s → SS G STK σ (c σ) s) :
    VP (H1 (G := G) (Gh := Gh) F) (.block [VG.Impl.MdStream.PPC64LE.mov .r3 .r26, .li .r5 1,
      VG.Impl.MdStream.PPC64LE.mov .r6 .r27]) (H1c (G := G) (Gh := Gh) F) := by
  refine VP.pub (H1.pub hF) [.r26, .r27] ⟨VG.Taint.hintOfSize VG.PPC64LE.taint 64 (Taint.ofRegs [.r28, .r26, .r27])
    (.block [VG.Impl.MdStream.PPC64LE.mov .r3 .r26, .li .r5 1, VG.Impl.MdStream.PPC64LE.mov .r6 .r27]), rfl⟩
    (fun σ₁ σ₂ s₁ s₂ h₁ h₂ r hr => ?_) fun σ s hs => ?_
  · obtain ⟨-, -, -, -, -, -, a26, a27, -⟩ := h₁
    obtain ⟨-, -, -, -, -, -, b26, b27, -⟩ := h₂
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [a26, b26]
    · rw [a27, b27]
  obtain ⟨s₀, h₀, K, sp, F₀, W, e26, e27, e4⟩ := hs
  refine WP.wr (exec_addi (by decide) (by decide)) fun s₁ u₁ sp₁ _ => ?_
  refine WP.wr (exec_li (by decide)) fun s₂ u₂ sp₂ _ => ?_
  refine WP.wr (exec_addi (by decide) (by decide)) fun t u sp₃ _ => WP.block_nil ⟨⟨s₀, h₀, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · refine ⟨fun r hr => ?_, by rw [u.rd, u₂.rd, u₁.rd, K.2.1], by rw [u.wr, u₂.wr, u₁.wr, K.2.2]⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [u.other _ hr.2.2.2.2.1, u₂.other _ hr.2.2.2.1, u₁.other _ hr.2.1, K.gpr (by simpa using hr)]
  · rw [sp₃, sp₂, sp₁, sp]
  · rw [u.mem, u₂.mem, u₁.mem]; exact F₀
  · rw [u.mem, u₂.mem, u₁.mem]; exact W
  · rw [u.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), e26]
  · rw [u.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), e27]
  · rw [u.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), e4]
  · rw [u.other _ (by decide), u₂.other _ (by decide), u₁.gpr, e26, BitVec.add_zero]
  · rw [u.other _ (by decide), u₂.gpr]; rfl
  · rw [u.gpr, u₂.other _ (by decide), u₁.other _ (by decide), e27, BitVec.add_zero]

/-- After the compression. -/
abbrev H2 (F : State → State → Prop) (σ s : State) : Prop :=
  ∃ s₀, F σ s₀ ∧ Keep hashRegs s₀ s ∧ s.sp = s₀.sp ∧
    Frame [G.rs sState (4 * Gh.k), G.rs (wB G.pLen) HO.P.so] s₀.mem s.mem ∧
    HO.md.stateAt s.mem (G.sa sState) = HO.md.compress HO.H0 (HO.md.blockAt s₀.mem (G.sa sMsg)) ∧
    s.gpr .r26 = G.sa sState

theorem H2.pub {F : State → State → Prop} {c : State → Cfg} (hF : ∀ σ s, F σ s → SS G STK σ (c σ) s) :
    Pub G (H2 HO (G := G) F) := fun σ s ⟨s₀, h₀, K, sp, _⟩ =>
  ⟨by rw [K.gpr (by decide)]; exact (hF σ s₀ h₀).gi.r28, by rw [sp]; exact (SS.pub hF σ s₀ h₀).2⟩

theorem hash2b_vp {F : State → State → Prop} {c : State → Cfg} (hF : ∀ σ s, F σ s → SS G STK σ (c σ) s) :
    VP (H1c (G := G) (Gh := Gh) F) (.call Gh.name Gh.code) (H2 HO (G := G) F) := by
  -- The regions the compression function is given.
  let rd : List Region := [⟨G.sa sMsg, HO.P.B * 1⟩]
  let wr : List Region := [⟨G.sa sState, HO.P.N⟩, ⟨G.sa (wB G.pLen), HO.P.so⟩]
  obtain ec : ∀ {s : State} {r : Reg}, r ∉ linkRegs → (s.callEntry.withRegions rd wr).gpr r = s.gpr r :=
    fun h => by rw [State.withRegions_gpr, State.callEntry_gpr _ h]
  obtain facts : ∀ σ s, H1c (G := G) (Gh := Gh) F σ s →
      (compressK HO.md).pre (s.callEntry.withRegions rd wr) ∧ Covers (rd ++ wr) (s.rd ++ s.wr) ∧
        Covers wr s.wr := by
    intro σ s ⟨⟨s₀, hs₀, K, _, _, _, _, _, e4⟩, e3, e5, e6⟩
    obtain h := hF σ s₀ hs₀
    have gi := h.gi
    have big := gi.wBig
    have fit := gi.scrFit
    obtain hB := HO.hB; have hN := HO.hN; have hso := HO.hso; have hk := HO.hk
    have := HO.hso0; have := HO.hk0
    have lens := gi.lens3
    obtain wBh : sState + 32 ≤ wB G.pLen := by rcases lens with e | e | e <;> rw [e] <;> decide
    obtain wW : 1024 ≤ 8 * wWords G.pLen := by rcases lens with e | e | e <;> rw [e] <;> decide
    have n0 : sState = 576 := rfl
    have n1 : sMsg = 512 := rfl
    have ws : s.wr = s₀.wr := K.2.2
    obtain hw : Covers wr s.wr := by
      rw [ws]
      refine Covers.pair (Covers.one (gi.inScr ?_ ?_)) (Covers.one (gi.inScr ?_ ?_)) <;> omega_arith
    refine ⟨?_, Covers.append_left (Covers.right (Covers.one (by
      rw [ws]; exact gi.inScr (by omega_using [big, hB, wW, n1]) (by omega_using [hB])))) hw.right, hw⟩
    simp only [compressK, State.withRegions_rd, State.withRegions_wr, ec (r := .r3) (by decide),
      ec (r := .r4) (by decide), ec (r := .r5) (by decide), ec (r := .r6) (by decide), e3, e4, e5, e6]
    rw [show (1 : BitVec 64).toNat = 1 from rfl]
    refine ⟨rfl, rfl, gi.sdisj ?_ ?_ ?_, gi.sdisj ?_ ?_ ?_, gi.sdisj ?_ ?_ ?_⟩ <;> omega_arith
  refine VP.of_ct (fun σ₁ σ₂ => RelCT.call HO.callee.verified HO.ct rd wr fun s₁ s₂ ⟨h₁, h₂⟩ => ?_)
    fun σ s hs => ?_
  · obtain ⟨p₁, c₁, w₁⟩ := facts σ₁ s₁ h₁
    obtain ⟨p₂, c₂, w₂⟩ := facts σ₂ s₂ h₂
    obtain ⟨⟨t₁, f₁, K₁, sp₁, -, -, -, -, a4⟩, a3, a5, a6⟩ := h₁
    obtain ⟨⟨t₂, f₂, K₂, sp₂, -, -, -, -, b4⟩, b3, b5, b6⟩ := h₂
    refine ⟨p₁, p₂, ⟨?_, ?_, ?_, ?_, ?_⟩, c₁, w₁, c₂, w₂⟩
    · rw [ec (by decide), ec (by decide), a3, b3]
    · rw [ec (by decide), ec (by decide), a4, b4]
    · rw [ec (by decide), ec (by decide), a5, b5]
    · rw [ec (by decide), ec (by decide), a6, b6]
    · show s₁.sp = s₂.sp
      rw [sp₁, sp₂, (SS.pub hF _ _ f₁).2, (SS.pub hF _ _ f₂).2]
  · obtain ⟨p, cv, wv⟩ := facts σ s hs
    obtain ⟨⟨s₀, hs₀, K, sp₀, F₀, W, e26, e27, e4⟩, e3, e5, e6⟩ := hs
    obtain h := hF σ s₀ hs₀
    have gi := h.gi
    have big := gi.wBig
    have fit := gi.scrFit
    obtain hN := HO.hN; have hso := HO.hso; have hB := HO.hB; have hk := HO.hk
    have lens := gi.lens3
    obtain wBh : sState + 32 ≤ wB G.pLen := by rcases lens with e | e | e <;> rw [e] <;> decide
    refine WP.call (k := compressK HO.md) HO.callee.verified p cv wv
      (fun s' hrd hwr hsp hf hg _ hpost => ?_) HO.callee.noFrames
    simp only [compressK, State.withRegions_mem, State.callEntry_mem,
      ec (r := .r3) (by decide), ec (r := .r4) (by decide), ec (r := .r5) (by decide), e3, e4, e5] at hpost
    rw [show (1 : BitVec 64).toNat = 1 from rfl, MdStream.Md.compressBlocks_one,
      HO.iv s.mem _ fun j hj => by rw [GP.sa_add]; exact W j hj] at hpost
    refine ⟨s₀, hs₀, ?_, by rw [hsp, sp₀], ?_, ?_, by rw [hg _ (by decide), e26]⟩
    · refine ⟨fun r hr => ?_, by rw [hrd, K.2.1], by rw [hwr, K.2.2]⟩
      obtain hp : r ∈ preserved := by revert hr; cases r <;> decide
      rw [hg r hp, K.gpr (by revert hr; cases r <;> decide)]
    · refine (F₀.mono (rs' := [G.rs sState (4 * Gh.k), G.rs (wB G.pLen) HO.P.so]) fun r hr => by
        simp only [List.mem_singleton] at hr; simp [hr]).trans (hf.sub fun r hr => ?_)
      simp only [wr, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨G.rs sState (4 * Gh.k), List.mem_cons_self, by rw [hN]; exact fun _ h => h⟩
      · exact ⟨G.rs (wB G.pLen) HO.P.so, by simp, fun _ h => h⟩
    · rw [hpost]
      refine congrArg (HO.md.compress HO.H0) ?_
      unfold VG.Proof.MdStream.Md.blockAt
      refine HO.md.parse_congr fun k hk => ?_
      rw [hB] at hk
      exact F₀.bytes (R := G.rs sMsg 64) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        have n0 : sState = 576 := rfl
        have n1 : sMsg = 512 := rfl
        exact gi.sdisj (by omega_using [n0, n1]) (by omega_using [big, wBh, n0, n1]) (by omega_arith)) (by show 64 ≤ 2 ^ 64; decide) hk

theorem out_length (k : Nat) (f : Nat → BitVec 32) :
    ((List.range k).flatMap fun j => MdStream.bytes32 true (f j)).length = 4 * k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [List.range_succ, List.flatMap_append, List.length_append, ih, List.flatMap_singleton,
      MdStream.bytes32_length]; omega_using []

/-- The block's bytes, as the compression function reads it. -/
theorem blockAt_eq {m : Mem} {p : Addr} {bs : List Byte} (h : Spec.Rsa.bytesAt m p 64 = bs) :
    HO.md.blockAt m p = HO.md.parse fun t => bs.getD t 0 := by
  unfold VG.Proof.MdStream.Md.blockAt
  refine HO.md.parse_congr fun k hk => ?_
  rw [HO.hB] at hk
  rw [← h]
  simp [Spec.Rsa.bytesAt, List.getD_eq_getElem?_getD, hk]

theorem hash3_vp {F Q : State → State → Prop} {c : State → Cfg} {dst : Nat} {msg : State → List Byte}
    (hF : ∀ σ s, F σ s → SS G STK σ (c σ) s)
    (hm : ∀ σ s, F σ s → (msg σ).length < 56 ∧ Spec.Rsa.bytesAt s.mem (G.sa sMsg) 64 = blk HO.md (msg σ))
    (hd1 : sState + 32 ≤ dst) (hd2 : dst + 32 ≤ wB G.pLen)
    (k : ∀ σ s t, F σ s → Keep hashRegs s t → t.sp = s.sp →
      Frame (G.rss [(sState, 32), (wB G.pLen, 1024), (dst, 4 * Gh.k)]) s.mem t.mem →
      Spec.Rsa.bytesAt t.mem (G.sa dst) (4 * Gh.k) = HO.H (msg σ) → Q σ t) :
    VP (H2 HO (G := G) F) (.block ([.addi .r28 .r28 dst] ++ VG.Impl.MdStream.PPC64LE.out32 Gh.k true ++
      [.subi .r28 .r28 dst])) Q := by
  refine VP.pub (H2.pub HO hF) [.r26] (HO.cert3 dst) (fun σ₁ σ₂ s₁ s₂ h₁ h₂ r hr => ?_) fun σ s hs => ?_
  · obtain ⟨-, -, -, -, -, -, e₁⟩ := h₁
    obtain ⟨-, -, -, -, -, -, e₂⟩ := h₂
    simp only [List.mem_singleton] at hr; subst hr; rw [e₁, e₂]
  obtain ⟨s₀, hs₀, K, sp₀, F₀, St, e26⟩ := hs
  obtain h := hF σ s₀ hs₀
  have gi := h.gi
  have big := gi.wBig
  have fit := gi.scrFit
  have hk := HO.hk
  have hk0 := HO.hk0
  have hso := HO.hso
  have lens := gi.lens3
  obtain wBl : wB G.pLen < 2 ^ 15 := by rcases lens with e | e | e <;> rw [e] <;> decide
  obtain wW : 1024 ≤ 8 * wWords G.pLen := by rcases lens with e | e | e <;> rw [e] <;> decide
  obtain r28 : s.gpr .r28 = G.scr := by rw [K.gpr (by decide)]; exact gi.r28
  rw [List.append_assoc, List.singleton_append]
  refine WP.wr (exec_addi (by decide) (by omega_using [hd2, wBl])) fun s₁ u₁ sp₁ _ => ?_
  obtain a28 : s₁.gpr .r28 = G.sa dst := by rw [u₁.gpr, r28]
  obtain a26 : s₁.gpr .r26 = G.sa sState := by rw [u₁.other _ (by decide), e26]
  obtain rd₁ : s₁.rd = s₀.rd := by rw [u₁.rd, K.2.1]
  obtain wr₁ : s₁.wr = s₀.wr := by rw [u₁.wr, K.2.2]
  refine WP.block_append (WP.mono (VG.Proof.MdStream.PPC64LE.out32_ok (n := Gh.k) true (by omega_using [hk])
    (by rw [a26, rd₁, wr₁]; exact gi.inRdWr (by omega_using [hd1, hd2, big, hk]) (by omega_using [hk0]))
    (by rw [a28, wr₁]; exact gi.inScr (by omega_using [hd2, big, hk]) (by omega_using [hk0]))
    (by rw [a26, a28]; exact gi.sdisj (by omega_using [hd1, hk]) (by omega_using [hd1, hd2, big, hk]) (by omega_using [hd2, big, hk])))
    fun s₂ ⟨g₂, rd₂, wr₂, sp₂, m₂⟩ => ?_)
  refine WP.wr (exec_subi (by decide) (by omega_using [hd2, wBl])) fun t u spt _ => WP.block_nil ?_
  rw [a28, a26, u₁.mem] at m₂
  obtain mt : t.mem = VG.WriteBytes.writeBytes s.mem (G.sa dst) (HO.md.digest (HO.md.stateAt s.mem (G.sa sState))) := by
    rw [u.mem, m₂, HO.digest]
  obtain dl : (HO.md.digest (HO.md.stateAt s.mem (G.sa sState))).length = 4 * Gh.k := by
    rw [HO.digest, out_length]
  refine k σ s₀ t hs₀ ⟨fun r hr => ?_, by rw [u.rd, rd₂, rd₁], by rw [u.wr, wr₂, wr₁]⟩
    (by rw [spt, sp₂, sp₁, sp₀]) ?_ ?_
  · by_cases h28 : r = .r28
    · subst h28
      rw [u.gpr, g₂ _ (by decide) (by decide), a28, gi.r28, GP.sa, BitVec.add_sub_cancel]
    · have h8 : r ≠ .r8 := fun e => hr (by rw [e]; decide)
      obtain h11 : r ≠ .r11 := fun e => hr (by rw [e]; decide)
      rw [u.other _ h28, g₂ _ h8 h11, u₁.other _ h28, K.gpr hr]
  · show Frame [G.rs sState 32, G.rs (wB G.pLen) 1024, G.rs dst (4 * Gh.k)] _ _
    refine (F₀.sub fun r hr => ?_).trans ?_
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨G.rs sState 32, List.mem_cons_self, Offset.sub _ (Nat.le_refl _) (by omega_using [hk])⟩
      · exact ⟨G.rs (wB G.pLen) 1024, by simp, Offset.sub _ (Nat.le_refl _) (by omega_using [hso])⟩
    · rw [mt]
      refine (VG.WriteBytes.writeBytes_frame _ _ _ (R := G.rs dst (4 * Gh.k)) ?_).mono (by simp)
      rw [dl]; exact Region.contains_self _ _
  · obtain ⟨ml, hb⟩ := hm σ s₀ hs₀
    obtain e := VG.Proof.Sha256.Stream.bytesAt_writeBytes s.mem (G.sa dst) 0
      (HO.md.digest (HO.md.stateAt s.mem (G.sa sState))) (by rw [dl]; omega_using [hk])
    rw [BitVec.add_zero, Nat.zero_add, dl] at e
    show Spec.Sha256.bytesAt _ _ _ = _
    rw [mt, e, St, blockAt_eq HO hb, ← HO.hash _ ml]; rfl

/-- `hash pLen Gh dst`: the digest of the message whose block is at `sMsg` into `dst`. -/
theorem hash_vp {F Q : State → State → Prop} {c : State → Cfg} {dst : Nat} {msg : State → List Byte}
    (hF : ∀ σ s, F σ s → SS G STK σ (c σ) s)
    (hm : ∀ σ s, F σ s → (msg σ).length < 56 ∧ Spec.Rsa.bytesAt s.mem (G.sa sMsg) 64 = blk HO.md (msg σ))
    (hd1 : sState + 32 ≤ dst) (hd2 : dst + 32 ≤ wB G.pLen)
    (k : ∀ σ s t, F σ s → Keep hashRegs s t → t.sp = s.sp →
      Frame (G.rss [(sState, 32), (wB G.pLen, 1024), (dst, 4 * Gh.k)]) s.mem t.mem →
      Spec.Rsa.bytesAt t.mem (G.sa dst) (4 * Gh.k) = HO.H (msg σ) → Q σ t) :
    VP F (hash G.pLen Gh dst) Q :=
  VP.seq (hash1_vp HO hF) (VP.seq (VP.seq (hash2a_vp hF) (hash2b_vp HO hF)) (hash3_vp HO hF hm hd1 hd2 k))

end

end VG.Proof.Dsa.PPC64LE.Gen

end

end

/-! # DSA parameter generation on PPC64LE: q

`qPart` (`qPart_vp`): the seed at `fSeed` copied before the block's padding
at `sMsg`, hashed into `sQ`, its top and low bits set (`shapeQ_vp`), and
tested. The claims after it: the padding, and q's bytes at `sQ`.
-/

@[expose] public section

namespace VG.Proof.Dsa.PPC64LE.Gen
open VG VG.PPC64LE
open VG.Impl.Dsa.PPC64LE.Generation
open VG.Proof.Ffdh.ParameterCandidate (shapedOctets)

/-- The seed at byte `k` of the tape. -/
abbrev seedAt (G : GP) (k : Nat) : List Byte := (G.seedsB.drop k).take G.qLen

/-- The block after a message of `n` bytes. -/
def padTail {B N L : Nat} (md : MdStream.Md B N L) (n : Nat) : List Byte :=
  [0x80] ++ List.replicate (55 - n) 0 ++ md.lenBytes n

/-- q's bytes, from the seed at `k`. -/
abbrev qBytes (G : GP) (k : Nat) : List Byte :=
  shapedOctets (Spec.Dsa.seedHash (8 * G.qLen) (seedAt G k)) 7

/-- The claims after q: the padding, and q's bytes at `sQ`. -/
abbrev qClaims {B N L : Nat} (md : MdStream.Md B N L) (G : GP) (k : Nat) : Claims :=
  [(sMsg + G.qLen, padTail md G.qLen), (sQ, qBytes G k)]

theorem padTail_length {B N L : Nat} (md : MdStream.Md B N L) {n : Nat} (hn : n < 56) (hL : L = 8) :
    (padTail md n).length = 64 - n := by
  simp only [padTail, List.length_append, List.length_cons, List.length_nil, List.length_replicate,
    md.lenBytes_length]
  omega_using [hn, hL]

section
variable {G : GP} {STK : Nat} {σ s : State} {V : Nat → BitVec 64} {LS : List Nat}

theorem GI.seedsFit (h : GI G STK σ V LS s) : G.seeds.toNat + G.seedsLen ≤ 2 ^ 64 := by
  have := h.pre.nW; rw [← h.hG]; exact this

/-- The seeds are apart from what the search changes. -/
theorem GI.seeds_apart (h : GI G STK σ V LS s) : ∀ r ∈ [G.rScr, rBelow σ STK], G.rSeeds.Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · rw [← h.hG]; exact h.pre.wC
  · rw [← h.hG]; exact h.pre.bW.symm

/-- The seed at `k`, in memory. -/
theorem GI.seedBytes (h : GI G STK σ V LS s) {k : Nat} (hk : k + G.qLen ≤ G.seedsLen) :
    Spec.Rsa.bytesAt s.mem (G.seeds + BitVec.ofNat 64 k) G.qLen = seedAt G k := by
  have fit := h.seedsFit
  obtain hw : Spec.Rsa.bytesAt s.mem G.seeds G.seedsLen = G.seedsB := by
    rw [VG.Proof.Dsa.Generation.frame_bytesAt h.frame h.seeds_apart (by dsimp only [GP.seedsLen, GP.seeds] at fit ⊢; omega_using [fit]), ← h.hG]; rfl
  obtain ⟨d, hd⟩ : ∃ d, G.seedsLen = k + G.qLen + d := ⟨G.seedsLen - k - G.qLen, by omega_using [hk]⟩
  show _ = (G.seedsB.drop k).take G.qLen
  rw [← hw, hd, VG.Proof.Dsa.Generation.bytesAt_append, VG.Proof.Dsa.Generation.bytesAt_append,
    List.append_assoc, List.drop_left' (by simp [Spec.Rsa.bytesAt]),
    List.take_left' (by simp [Spec.Rsa.bytesAt])]

/-- The seed at `k`, as a source of a copy. -/
theorem GI.seedSrc (h : GI G STK σ V LS s) {k : Nat} (hk : k + G.qLen ≤ G.seedsLen) (hq0 : 0 < G.qLen) :
    InRegions (s.rd ++ s.wr) (G.seeds + BitVec.ofNat 64 k) G.qLen ∧
      (G.seeds + BitVec.ofNat 64 k).toNat + G.qLen ≤ 2 ^ 64 ∧
      Region.Disjoint ⟨G.seeds + BitVec.ofNat 64 k, G.qLen⟩ G.rScr := by
  have fit := h.seedsFit
  obtain sub : Region.Sub ⟨G.seeds + BitVec.ofNat 64 k, G.qLen⟩ G.rSeeds := Offset.sub_base _ hk
  obtain sC := h.pre.wC; rw [h.hG] at sC
  refine ⟨⟨G.rSeeds, ?_, Offset.contains_base _ hk (by omega_using [hk, hq0, fit])⟩, ?_, sC.sub_left sub⟩
  · rw [h.rd, h.pre.rd, h.hG]; simp
  · rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show k < 2 ^ 64 by omega_using [hk, hq0, fit]),
      Nat.mod_eq_of_lt (by omega_using [hk, hq0, fit])]
    omega_using [hk, fit]

end

/-! ## q's top and low bits -/

/-- The bit operations of the block. -/
abbrev shapeOps (N : Nat) : List Instr :=
  [.lbz .r0 .r28 sQ, .ori .r0 .r0 0x80, .stb .r0 .r28 sQ,
    .lbz .r0 .r28 (sQ + N - 1), .ori .r0 .r0 1, .stb .r0 .r28 (sQ + N - 1)]

theorem or_byte (b : Byte) (v : BitVec 16) :
    (b.setWidth 64 ||| v.setWidth 64).setWidth 8 = b ||| v.setWidth 8 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_setWidth, BitVec.getLsbD_or]
  simp [hi, show i < 64 by omega_using [hi], show i < 16 by omega_using [hi]]

/-- A claim added after a step that kept a stage. -/
theorem SS.addCl {G : GP} {STK : Nat} {σ t : State} {c : Cfg} (h : SS G STK σ c t) {o : Nat} {bs : List Byte}
    (e : Spec.Rsa.bytesAt t.mem (G.sa o) bs.length = bs) (ok : ClOk G (o, bs)) :
    SS G STK σ { c with cl := (o, bs) :: c.cl } t :=
  ⟨h.gi, h.sb.cons e, fun y hy => by
    rcases List.mem_cons.mp hy with rfl | hy
    · exact ok
    · exact h.clOk y hy, h.arrs, h.liveOk, h.ksl, h.kslOk⟩

section
variable {G : GP} {STK : Nat}

theorem shapeQ_vp {P Q : State → State → Prop} {c : State → Cfg} {N : Nat} {bs : List Byte}
    (hF : ∀ σ s, P σ s → SS G STK σ (c σ) s) (hN : 2 ≤ N) (hN' : N ≤ 32)
    (hb : ∀ σ s, P σ s → Spec.Rsa.bytesAt s.mem (G.sa sQ) N = bs)
    (k : ∀ σ s t, P σ s → Keep [.r0] s t → t.sp = s.sp → Frame [G.rs sQ N] s.mem t.mem →
      Spec.Rsa.bytesAt t.mem (G.sa sQ) N = shapedOctets bs 7 → Q σ t) :
    VP P (.block (shapeOps N)) Q := by
  refine VP.pub (SS.pub hF) [] ⟨VG.Taint.hintOfSize VG.PPC64LE.taint 64 (Taint.ofRegs [.r28])
      (.block (shapeOps 20)), rfl⟩ (fun _ _ _ _ _ _ _ h => absurd h (by simp)) fun σ s hs => ?_
  have h := hF σ s hs
  have gi := h.gi
  have big := gi.wBig
  have fit := gi.scrFit
  have lens := gi.lens3
  have wBh : sQ + 32 ≤ wB G.pLen := by rcases lens with e | e | e <;> rw [e] <;> decide
  have nq : sQ = 608 := rfl
  have w : ∀ j < N, InRegions s.wr (G.sa (sQ + j)) 1 := fun j hj => gi.inScr (by omega_using [hN', big, wBh, hj])
  have r_of : ∀ j < N, InRegions (s.rd ++ s.wr) (G.sa (sQ + j)) 1 := fun j hj => gi.inRdWr (by omega_using [hN', big, wBh, hj])
  have a0 : s.gpr .r28 + BitVec.ofNat 64 sQ = G.sa sQ := by rw [gi.r28]
  have aN : s.gpr .r28 + BitVec.ofNat 64 (sQ + N - 1) = G.sa (sQ + (N - 1)) := by
    rw [gi.r28, show sQ + N - 1 = sQ + (N - 1) by omega_using [hN]]
  refine WP.sp_eq ?_
  refine wp_lbz (by decide) (by omega_using [nq]) a0 (by simpa using r_of 0 (by omega_using [hN])) fun s₁ u₁ => ?_
  refine WP.wr exec_ori fun s₂ u₂ _ _ => ?_
  refine wp_stb (a := G.sa sQ) (by decide) (by omega_using [nq])
    (by rw [u₂.other _ (by decide), u₁.other _ (by decide)]; exact a0)
    (by rw [u₂.wr, u₁.wr]; simpa using w 0 (by omega_using [hN])) fun s₃ m₃ => ?_
  have a3 : s₃.gpr .r28 + BitVec.ofNat 64 (sQ + N - 1) = G.sa (sQ + (N - 1)) := by
    rw [m₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide)]; exact aN
  refine wp_lbz (by decide) (by omega_using [hN', nq]) a3
    (by rw [m₃.rd, m₃.wr, u₂.rd, u₂.wr, u₁.rd, u₁.wr]; exact r_of _ (by omega_using [hN])) fun s₄ u₄ => ?_
  refine WP.wr exec_ori fun s₅ u₅ _ _ => ?_
  refine wp_stb (a := G.sa (sQ + (N - 1))) (by decide) (by omega_using [hN', nq])
    (by rw [u₅.other _ (by decide), u₄.other _ (by decide)]; exact a3)
    (by rw [u₅.wr, u₄.wr, m₃.wr, u₂.wr, u₁.wr]; exact w _ (by omega_using [hN])) fun t m₆ => WP.block_nil fun sp => ?_
  have K : Keep [.r0] s t := ⟨fun r hr => by
      have hr : r ≠ .r0 := by simpa using hr
      rw [m₆.gpr, u₅.other _ hr, u₄.other _ hr, m₃.gpr, u₂.other _ hr, u₁.other _ hr],
    by rw [m₆.rd, u₅.rd, u₄.rd, m₃.rd, u₂.rd, u₁.rd], by rw [m₆.wr, u₅.wr, u₄.wr, m₃.wr, u₂.wr, u₁.wr]⟩
  have m₃' : s₃.mem = s.mem.writeW (G.sa sQ) (s.mem (G.sa sQ) ||| 128#8) := by
    rw [m₃.mem, u₂.gpr, u₁.gpr, u₂.mem, u₁.mem, or_byte]; rfl
  have b₃ : s₃.mem (G.sa (sQ + (N - 1))) = s.mem (G.sa (sQ + (N - 1))) := by
    rw [m₃', write1_apply, ite_eq_right]
    intro hlt
    have e0 : G.sa (sQ + (N - 1)) - G.sa sQ = 0 :=
      BitVec.eq_of_toNat_eq (by have : (0 : BitVec 64).toNat = 0 := rfl; omega)
    apply Offset.add_ofNat_ne G.scr (a := sQ + (N - 1)) (b := sQ) (by omega_using [hN', nq]) (by omega_using [nq]) (by omega_using [hN])
    show G.sa (sQ + (N - 1)) = G.sa sQ
    rw [← BitVec.sub_add_cancel (G.sa (sQ + (N - 1))) (G.sa sQ), e0]; simp
  have mt : t.mem = (s.mem.writeW (G.sa sQ) (s.mem (G.sa sQ) ||| 128#8)).writeW
      (G.sa sQ + BitVec.ofNat 64 (N - 1)) (s.mem (G.sa sQ + BitVec.ofNat 64 (N - 1)) ||| 1#8) := by
    rw [m₆.mem, u₅.gpr, u₄.gpr, u₅.mem, u₄.mem, b₃, or_byte, ← m₃', GP.sa_add]; rfl
  have hb' := hb σ s hs
  have bl : bs.length = N := by rw [← hb']; simp [Spec.Rsa.bytesAt]
  refine k σ s t hs K sp ?_ ?_
  · rw [mt, GP.sa_add]
    have c0 : (G.rs sQ N).Contains (G.sa sQ) (8 / 8) :=
      Offset.contains G.scr (d := sQ) (n := 1) (e := sQ) (k := N) (Nat.le_refl _) (by omega_using [hN]) (by omega_using [hN', nq])
    have c1 : (G.rs sQ N).Contains (G.sa (sQ + (N - 1))) (8 / 8) :=
      Offset.contains G.scr (d := sQ + (N - 1)) (n := 1) (e := sQ) (k := N) (by omega_using []) (by omega_using [hN]) (by omega_using [hN', nq])
    exact Frame.writeW (r := G.rs sQ N) (w := 8) (Frame.writeW (r := G.rs sQ N) (w := 8) (Frame.refl _ _)
      List.mem_cons_self _ c0) List.mem_cons_self _ c1
  · rw [mt, ← bl]
    refine VG.Proof.Dsa.Generation.qShape_memory (by omega_using [hN, bl]) (by omega_using [hN', bl]) fun i hi => ?_
    rw [← hb']
    simp [Spec.Rsa.bytesAt, List.getD_eq_getElem?_getD, bl ▸ hi]

end

/-! ## q -/

section
variable {G : GP} {c : Cfg} {X : State → Prop}

/-- q from the seed at `k`, tested with the witnesses from `u`. -/
theorem qPart_vp {g : Geo} (HO : HashOk g.G) {L : Impl.Dsa.ProbablePrime.Layout} (ok : PrimeOk L g.qCode)
    (hlq : (G.pLen = 128 ∧ G.qLen = 20) ∨ (G.pLen = 256 ∧ G.qLen = 32) ∨ (G.pLen = 384 ∧ G.qLen = 32))
    (hp : g.pLen = G.pLen) (hq : g.qLen = G.qLen) (hk4 : 4 * g.G.k = G.qLen)
    (hH : ∀ m, HO.H m = Spec.Dsa.seedHash (8 * G.qLen) m) (hwl : G.witB.length = G.witLen)
    (hsb : G.seedsB.length = G.seedsLen)
    (hLb : L.bits = 8 * G.qLen) (hLc : L.candidate = g.qCand)
    (hsize : L.size ≤ 8 * wWords G.pLen) (hL : ∀ r ∈ L.scratch, r.1 + r.2 ≤ 8 * wWords G.pLen)
    (hcand : L.candidate + L.bits / 8 ≤ 8 * wWords G.pLen) (hcand15 : wB G.pLen + L.candidate < 2 ^ 15)
    {k u : Nat} (hk : k + G.qLen ≤ G.seedsLen) (hu : u ≤ G.witLen)
    (hS : fSeed ∈ c.LS) (hSv : c.V fSeed = G.seeds + BitVec.ofNat 64 k)
    (hU : fUsed ∈ c.LS) (hUv : c.V fUsed = BitVec.ofNat 64 u)
    (hU' : ∀ o ∈ c.LS, fUsedOut + 8 ≤ o ∨ o + 8 ≤ fUsedOut) (hU88 : fUsedOut ∉ c.LS)
    (hpad : (sMsg + G.qLen, padTail HO.md G.qLen) ∈ c.cl) :
    VP (St G c X) g.qPart
      (St G (testCfg c (qClaims HO.md G k) G.witLen
        (Spec.Dsa.probablePrime (Spec.Dsa.qCandidate (8 * G.qLen) (seedAt G k)) (G.witB.drop u))) X) := by
  obtain hq0 : 0 < G.qLen := by omega_arith
  obtain hq56 : G.qLen < 56 := by omega_arith
  obtain hqk : G.qLen ≤ 32 := by omega_arith
  obtain pl : (padTail HO.md G.qLen).length = 64 - G.qLen := padTail_length HO.md hq56 HO.hL
  obtain hsl : (seedAt G k).length = G.qLen := by
    simp only [seedAt, List.length_take, List.length_drop, hsb]; omega_arith
  -- The hash and q.
  obtain hHl : (HO.H (seedAt G k)).length = G.qLen := by
    rw [HO.hash _ (by omega_arith), HO.md.digest_length, HO.hN, hk4]
  obtain hne : HO.H (seedAt G k) ≠ [] := fun e => by rw [e] at hHl; simp at hHl; omega_arith
  obtain qb : shapedOctets (HO.H (seedAt G k)) 7 = qBytes G k := by rw [hH]
  obtain qbl : (qBytes G k).length = G.qLen := by
    rw [← qb, shapedOctets, VG.Proof.Ffdh.ParameterCandidate.lastOne_length
      (by rw [← List.length_pos_iff, VG.Proof.Ffdh.ParameterCandidate.topCut_length hne]; omega_arith),
      VG.Proof.Ffdh.ParameterCandidate.topCut_length hne, hHl]
  obtain hqc : Spec.Dsa.decodeBE (qBytes G k) = Spec.Dsa.qCandidate (8 * G.qLen) (seedAt G k) :=
    VG.Proof.Dsa.Generation.qCandidate_octets (by omega_arith) _ (by rw [← hH, hHl])
  rw [← hqc]
  obtain hwB : sQ + 32 ≤ wB G.pLen := by rcases hlq with ⟨e, _⟩ | ⟨e, _⟩ | ⟨e, _⟩ <;> rw [e] <;> decide
  obtain hkB : sQ + 32 ≤ kB G.pLen := by rcases hlq with ⟨e, _⟩ | ⟨e, _⟩ | ⟨e, _⟩ <;> rw [e] <;> decide
  obtain hkw : kB G.pLen ≤ wB G.pLen := by simp only [wB]; omega_using []
  obtain hWW : 1024 ≤ 8 * wWords G.pLen := by rcases hlq with ⟨e, _⟩ | ⟨e, _⟩ | ⟨e, _⟩ <;> rw [e] <;> decide
  have nM : sMsg = 512 := rfl
  have nS : sState = 576 := rfl
  have nQ : sQ = 608 := rfl
  have nE : hEnd = 352 := rfl
  generalize hpd : padTail HO.md G.qLen = pad at hpad pl
  generalize hsd : seedAt G k = sd at hsl hHl hne qb
  let c1 : Cfg := { c with cl := [(sMsg, sd), (sMsg + G.qLen, pad)] }
  let c2 : Cfg := { c with cl := [(sMsg + G.qLen, pad), (sQ, HO.H sd)] }
  let c3 : Cfg := { c with cl := [(sMsg + G.qLen, pad), (sQ, qBytes G k)] }
  unfold Geo.qPart
  simp only [VG.Impl.Rsa.PPC64LE.Keys.seqs]
  rw [hq, hp]
  refine VP.seq (G := St G c1 X) ?_ (VP.seq (G := St G c2 X) ?_ (VP.seq (G := St G c3 X) ?_ ?_))
  · -- The seed, before the padding.
    refine copyIn_vp (c := fun _ => c) (fun σ s h => h.1) hq0 (by omega_using [hlq]) (by decide) (by decide) (by decide)
      (P := G.seeds + BitVec.ofNat 64 k) (fun σ s h => (h.1.gi.slotV hS).trans hSv)
      (fun σ s h => by have := h.1.gi.wBig; simp only [ClOk, List.length_replicate]; omega_using [hlq, hk4, hLc, hsize, hcand, hcand15, hk, hq0, hq56, hqk, hwB, hkB, hkw, hWW, nM, nQ, nE, this])
      (fun σ s h => h.1.gi.seedSrc hk hq0) fun σ s t ⟨h, x⟩ h' _ e => ⟨?_, x⟩
    rw [h.gi.seedBytes hk, hsd] at e
    refine (h'.addCl (o := sMsg) (bs := sd) (by rw [hsl]; exact e)
      (by have := h.gi.wBig; simp only [ClOk, hsl]; omega_using [hlq, hk4, hLc, hsize, hcand, hcand15, hk, hq0, hq56, hqk, hwB, hkB, hkw, hWW, nM, nQ, nE, this])).mono (fun o ho => ⟨ho, rfl⟩) (fun y hy => ?_) (fun j hj => ⟨hj, rfl⟩)
      (fun d hd => ⟨hd, rfl⟩)
    simp only [c1, List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl | rfl
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (List.mem_filter.mpr ⟨hpad, by simp only [Apart, decide_eq_true_eq]; omega_using []⟩)
  · -- The hash.
    refine hash_vp HO (c := fun _ => c1) (fun σ s h => h.1) (msg := fun _ => sd) (dst := sQ)
      (fun σ s ⟨h, _⟩ => ⟨by omega_using [hlq, hsl], ?_⟩) (by decide) hwB fun σ s t ⟨h, x⟩ K sp f e => ⟨?_, x⟩
    · have b1 := h.sb (sMsg, sd) (by simp [c1])
      obtain b2 := h.sb (sMsg + G.qLen, pad) (by simp [c1])
      rw [show (64 : Nat) = sd.length + pad.length by omega_using [hlq, pl, hsl], VG.Proof.Dsa.Generation.bytesAt_append, b1]
      obtain a : VG.Proof.Bignum.off (G.sa sMsg) sd.length = G.sa (sMsg + G.qLen) := by
        rw [VG.Proof.Bignum.off, GP.sa_add, hsl]
      rw [a, b2, ← hpd]
      simp only [blk, padTail, hsl, List.append_assoc]
    have big := h.gi.wBig
    refine h.of_scrs K sp (os := [(sState, 32), (wB G.pLen, 1024), (sQ, 4 * g.G.k)]) (fun p hp => ?_)
      (f.mono fun r hr => List.mem_append_left _ hr) fun y hy => ?_
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl <;> simp only [ClOk, List.length_replicate] <;> omega_arith
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl | rfl
    · refine .inl ⟨by simp [c1], fun p hp => ?_⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl <;> simp only [Apart, pl] <;> omega_arith
    · exact .inr ⟨by rw [hHl, ← hk4]; exact e, by simp only [ClOk, hHl]; omega_using [hlq, hk4, hcand15, hk, hq0, hq56, hqk, hwB, hkB, hkw, nQ, nE, big]⟩
  · -- q's shape.
    refine shapeQ_vp (c := fun _ => c2) (fun σ s h => h.1) (N := G.qLen) (by omega_using [hlq]) (by omega_using [hlq])
      (bs := HO.H sd) (fun σ s ⟨h, _⟩ => by have := h.sb (sQ, HO.H sd) (by simp [c2]); rwa [hHl] at this)
      fun σ s t ⟨h, x⟩ K sp f e => ⟨?_, x⟩
    have big := h.gi.wBig
    refine h.of_scrs K sp (os := [(sQ, G.qLen)]) (fun p hp => ?_)
      (f.mono fun r hr => List.mem_append_left _ hr) fun y hy => ?_
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      subst hp; simp only [ClOk, List.length_replicate]; omega_using [hlq, hk4, hcand15, hk, hq0, hq56, hqk, hwB, hkB, hkw, nQ, nE, big]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl | rfl
    · refine .inl ⟨by simp [c2], fun p hp => ?_⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      subst hp; simp only [Apart, pl]; omega_using [hlq, nM, nQ]
    · exact .inr ⟨by rw [qbl, ← qb]; exact e, by simp only [ClOk, qbl]; omega_using [hlq, hk4, hcand15, hk, hq0, hq56, hqk, hwB, hkB, hkw, nQ, nE, big]⟩
  · -- The test.
    obtain hqs := VG.Proof.Dsa.Generation.qCandidate_shape (n := 8 * G.qLen) (by omega_arith) (seedAt G k)
    obtain hbl := VG.Proof.Dsa.Generation.qCandidate_bitLength (n := 8 * G.qLen) (by omega_arith) (seedAt G k)
    rw [← hqc] at hqs hbl
    have := test_vp (X := X) (c := c3) (cb := qBytes G k) (src := sQ) (cl' := qClaims HO.md G k)
      (name := g.qName) ok hu hU hUv hwl hsize hL hcand hcand15 (by simp [c3]) (by rw [qbl]; omega_using [hlq, hkB])
      (by rw [qbl, hLb]; omega_using []) (by rw [qbl]; omega_using [hlq]) (by rw [qbl]; omega_using [hlq]) (by decide) hqs.1 (by rw [hbl, hLb])
      hU' hU88 fun y hy => ?_
    · rwa [qbl, hLc] at this
    simp only [qClaims, List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl | rfl
    · refine ⟨List.mem_cons_of_mem _ (List.mem_filter.mpr ⟨by simp [c3, hpd], ?_⟩), fun r _ => .inl ?_⟩
      · simp only [Apart, hpd, pl, decide_eq_true_eq]; omega_using [hlq, hk4, hLb, hLc, hsize, hcand, hcand15, hk, hq0, hq56, hqk, qbl, hwB, hkB, hkw, hWW, nM, nQ]
      · simp only [hpd, pl]; omega_using [hlq, hk4, hLc, hcand, hcand15, hk, hq0, hq56, hqk, hwB, hkB, hkw, nM, nQ]
    · refine ⟨List.mem_cons_of_mem _ (List.mem_filter.mpr ⟨by simp [c3], ?_⟩), fun r _ => .inl ?_⟩
      · simp only [Apart, qbl, decide_eq_true_eq]; omega_using [hlq, hk4, hLc, hcand, hcand15, hk, hq0, hq56, hqk, hwB, hkB, hkw, nQ]
      · simp only [qbl]; omega_using [hlq, hwB]

end

end VG.Proof.Dsa.PPC64LE.Gen

end

end

/-! ### `Dsa.PPC64LE.Gen.PHash`, which only this module used -/

section

/-! ### `Dsa.PPC64LE.Gen.Add`, which only this module used -/

section

/-! # DSA parameter generation on PPC64LE: `seed + offset + j`

The loop of `seedAdd` adds `r4` to the `r6` big-endian bytes ending at `r3`,
a byte at a time from the last, the carry and the addend's higher bytes on
in `r4` (`addLoop_ok`), against `Spec.Dsa.encodeBE n (decodeBE bytes + addend)`
(`Proof.Dsa.Generation.seedAdd_snoc`).
-/

@[expose] public section

namespace VG.Proof.Dsa.PPC64LE.Gen
open VG VG.PPC64LE
open VG.Impl.Dsa.PPC64LE.Generation

/-- One step: the byte at `r3` := its sum with `r4`, `r4` := that sum's higher bits. -/
theorem addStep_ok {s : State} {a : Addr} (ha : s.gpr .r3 = a) (hw : InRegions s.wr a 1)
    (hc : (s.gpr .r4).toNat < 2 ^ 63) :
    WP isa (.block addStep) s fun t =>
      t.mem = s.mem.writeW a (BitVec.ofNat 8 ((s.mem a).toNat + (s.gpr .r4).toNat)) ∧
      t.gpr .r4 = BitVec.ofNat 64 (((s.mem a).toNat + (s.gpr .r4).toNat) / 256) ∧
      t.gpr .r3 = s.gpr .r3 - 1 ∧ t.gpr .r6 = s.gpr .r6 - 1 ∧
      Keep [.r3, .r4, .r5, .r6] s t ∧ t.sp = s.sp := by
  obtain hr : InRegions (s.rd ++ s.wr) a 1 := let ⟨r, hr, hc⟩ := hw; ⟨r, List.mem_append_right _ hr, hc⟩
  refine WP.sp_eq ?_
  unfold addStep
  refine wp_lbz (by decide) (by decide) (by rw [ha, BitVec.add_zero]) hr fun s₁ u₁ => ?_
  refine WP.wr exec_add fun s₂ u₂ _ _ => ?_
  obtain v : s₂.gpr .r5 = BitVec.ofNat 64 ((s.mem a).toNat + (s.gpr .r4).toNat) := by
    rw [u₂.gpr, u₁.gpr, u₁.other .r4 (by decide)]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    have := (s.mem a).isLt
    rw [Nat.mod_eq_of_lt (by omega_using [] : (s.mem a).toNat < 2 ^ 64)]
  refine wp_stb (a := a) (by decide) (by decide)
    (by rw [u₂.other .r3 (by decide), u₁.other .r3 (by decide), ha, BitVec.add_zero])
    (by rw [u₂.wr, u₁.wr]; exact hw) fun s₃ m₃ => ?_
  refine WP.wr (exec_lsr_d (by decide)) fun s₄ u₄ _ _ => ?_
  refine WP.wr (exec_subi (by decide) (by decide)) fun s₅ u₅ _ _ => ?_
  refine WP.wr (exec_subi (by decide) (by decide)) fun t u₆ _ _ => WP.block_nil fun sp => ⟨?_, ?_, ?_, ?_, ?_, sp⟩
  · rw [u₆.mem, u₅.mem, u₄.mem, m₃.mem, v, u₂.mem, u₁.mem]
    congr 1
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    rw [Nat.mod_mod_of_dvd _ (by decide)]
  · have bl := (s.mem a).isLt
    rw [u₆.other .r4 (by decide), u₅.other .r4 (by decide), u₄.gpr, m₃.gpr, v]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [hc]),
      Nat.mod_eq_of_lt (by omega_using []), Nat.shiftRight_eq_div_pow]
  · rw [u₆.other .r3 (by decide), u₅.gpr, u₄.other .r3 (by decide), m₃.gpr, u₂.other .r3 (by decide),
      u₁.other .r3 (by decide)]; rfl
  · rw [u₆.gpr, u₅.other .r6 (by decide), u₄.other .r6 (by decide), m₃.gpr, u₂.other .r6 (by decide),
      u₁.other .r6 (by decide)]; rfl
  · refine ⟨fun r hr => ?_, by rw [u₆.rd, u₅.rd, u₄.rd, m₃.rd, u₂.rd, u₁.rd],
      by rw [u₆.wr, u₅.wr, u₄.wr, m₃.wr, u₂.wr, u₁.wr]⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [u₆.other _ hr.2.2.2, u₅.other _ hr.1, u₄.other _ hr.2.1, m₃.gpr, u₂.other _ hr.2.2.1,
      u₁.other _ hr.2.2.1]

/-- After `i` of the `n` bytes, with `c` carried. -/
structure AddInv (s₀ : State) (base : Addr) (n add i c : Nat) (t : State) : Prop where
  le : i ≤ n
  r3 : t.gpr .r3 + BitVec.ofNat 64 i = base + BitVec.ofNat 64 (n - 1)
  r4 : t.gpr .r4 = BitVec.ofNat 64 c
  cle : c ≤ add
  r6 : t.gpr .r6 = BitVec.ofNat 64 (n - i)
  frame : Frame [⟨base, n⟩] s₀.mem t.mem
  pre : ∀ j < n - i, t.mem (base + BitVec.ofNat 64 j) = s₀.mem (base + BitVec.ofNat 64 j)
  enc : Spec.Dsa.encodeBE n (Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s₀.mem base n) + add) =
    Spec.Dsa.encodeBE (n - i) (Spec.Dsa.decodeBE ((Spec.Rsa.bytesAt s₀.mem base n).take (n - i)) + c) ++
      Spec.Rsa.bytesAt t.mem (base + BitVec.ofNat 64 (n - i)) i
  keep : Keep [.r3, .r4, .r5, .r6] s₀ t
  sp : t.sp = s₀.sp

/-- One byte of the addition, from the last: `seedAdd_snoc` on a prefix of the bytes. -/
theorem encode_step (m : Mem) (p : Addr) {n k : Nat} (hk : k < n) (c : Nat) :
    Spec.Dsa.encodeBE (k + 1) (Spec.Dsa.decodeBE ((Spec.Rsa.bytesAt m p n).take (k + 1)) + c) =
      Spec.Dsa.encodeBE k (Spec.Dsa.decodeBE ((Spec.Rsa.bytesAt m p n).take k) +
        ((m (p + BitVec.ofNat 64 k)).toNat + c) / 256) ++
        [BitVec.ofNat 8 ((m (p + BitVec.ofNat 64 k)).toNat + c)] := by
  obtain e : (Spec.Rsa.bytesAt m p n).take (k + 1) = (Spec.Rsa.bytesAt m p n).take k ++ [m (p + BitVec.ofNat 64 k)] := by
    rw [List.take_add_one, List.getElem?_eq_getElem (by simp [Spec.Rsa.bytesAt]; exact hk)]
    simp [Spec.Rsa.bytesAt]
  obtain l : ((Spec.Rsa.bytesAt m p n).take k).length = k := by simp [Spec.Rsa.bytesAt]; omega_using [hk]
  have := VG.Proof.Dsa.Generation.seedAdd_snoc ((Spec.Rsa.bytesAt m p n).take k) (m (p + BitVec.ofNat 64 k)) c
  rw [l] at this
  rw [e, this]

theorem bytesAt_cons (m : Mem) (p : Addr) (k i : Nat) :
    Spec.Rsa.bytesAt m (p + BitVec.ofNat 64 k) (i + 1) =
      m (p + BitVec.ofNat 64 k) :: Spec.Rsa.bytesAt m (p + BitVec.ofNat 64 (k + 1)) i := by
  simp only [Spec.Rsa.bytesAt, List.range_succ_eq_map, List.map_cons, List.map_map]
  rw [BitVec.add_zero]
  congr 1
  refine List.map_congr_left fun j _ => ?_
  show m (p + BitVec.ofNat 64 k + BitVec.ofNat 64 (j + 1)) = m (p + BitVec.ofNat 64 (k + 1) + BitVec.ofNat 64 j)
  rw [BitVec.add_assoc, BitVec.add_assoc, ← BitVec.ofNat_add, ← BitVec.ofNat_add]
  congr 3; omega_using []

theorem addBody_ok {s₀ t : State} {base : Addr} {n add i c : Nat} (hn : n < 2 ^ 15)
    (hfit : base.toNat + n ≤ 2 ^ 64) (hadd : add < 2 ^ 32) (hw : InRegions s₀.wr base n)
    (h : AddInv s₀ base n add i c t) (hi : i < n) :
    WP isa (.block addStep) t fun u =>
      AddInv s₀ base n add (i + 1) (((t.mem (base + BitVec.ofNat 64 (n - 1 - i))).toNat + c) / 256) u ∧
        (u.gpr .r6 != 0) = decide (i + 1 ≠ n) := by
  obtain hj : n - 1 - i < n := by omega
  obtain ea : t.gpr .r3 = base + BitVec.ofNat 64 (n - 1 - i) := by
    have e := h.r3
    rw [show n - 1 = (n - 1 - i) + i by omega, BitVec.ofNat_add, ← BitVec.add_assoc] at e
    have := congrArg (· - BitVec.ofNat 64 i) e
    simpa only [BitVec.add_sub_cancel] using this
  obtain hw1 : InRegions t.wr (base + BitVec.ofNat 64 (n - 1 - i)) 1 := by
    rw [h.keep.2.2]
    exact Covers.one hw _ _ ⟨_, List.mem_singleton_self _, Offset.contains_base _ (by omega) (by omega)⟩
  obtain bl := (t.mem (base + BitVec.ofNat 64 (n - 1 - i))).isLt
  obtain c32 : c < 2 ^ 32 := by have := h.cle; omega
  refine WP.mono (addStep_ok ea hw1 (by rw [h.r4, BitVec.toNat_ofNat]; omega)) ?_
  rintro u ⟨mu, r4, r3, r6, Ku, spu⟩
  rw [h.r4, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at mu r4
  refine ⟨⟨by omega, ?_, r4, ?_, ?_, ?_, ?_, ?_, (h.keep.trans Ku).mono (by simp), by rw [spu, h.sp]⟩, ?_⟩
  · rw [r3, ← h.r3, BitVec.ofNat_add, ← BitVec.add_assoc, BitVec.add_assoc (t.gpr .r3 - 1),
      BitVec.add_comm (BitVec.ofNat 64 i), ← BitVec.add_assoc]
    show t.gpr .r3 - 1 + 1 + _ = _
    rw [BitVec.sub_add_cancel]
  · have := h.cle; rcases Nat.eq_zero_or_pos c with rfl | hc0 <;> omega
  · have e : BitVec.ofNat 64 (n - i) - 1 = BitVec.ofNat 64 (n - (i + 1)) := count_sub (by omega)
    rw [r6, h.r6, e]
  · rw [mu]
    exact h.frame.writeW List.mem_cons_self _ (Offset.contains_base _ (by omega) (by omega))
  · intro j hj'
    rw [mu, VG.WriteBytes.writeW8_apply, ite_eq_right (fun e => by
      have := Offset.add_ofNat_ne base (a := j) (b := n - 1 - i) (by omega) (by omega) (by omega)
      exact this e)]
    exact h.pre j (by omega)
  · rw [h.enc, show n - i = (n - 1 - i) + 1 by omega, encode_step _ _ (by omega), ← h.pre (n - 1 - i) (by omega),
      show n - (i + 1) = n - 1 - i by omega, bytesAt_cons, List.append_assoc, List.singleton_append]
    congr 2
    · rw [mu, VG.WriteBytes.writeW8_apply, ite_eq_left rfl]
    · refine List.map_congr_left fun k hk => ?_
      obtain hk := List.mem_range.mp hk
      rw [mu, VG.WriteBytes.writeW8_apply, ite_eq_right (fun e => by
        rw [Offset.add_add] at e
        exact Offset.add_ofNat_ne base (a := n - 1 - i + 1 + k) (b := n - 1 - i) (by omega) (by omega)
          (by omega) e)]
  · have e : BitVec.ofNat 64 (n - i) - 1 = BitVec.ofNat 64 (n - (i + 1)) := count_sub (by omega)
    rw [r6, h.r6, e]
    exact count_nz (by omega) (by omega)

/-- The loop of `seedAdd`: the `n` big-endian bytes at `base`, `r3` at their
last, plus `r4`, the count in `r6`. -/
theorem addLoop_ok {s : State} {base : Addr} {n add : Nat} (hn : 0 < n) (hn15 : n < 2 ^ 15)
    (hfit : base.toNat + n ≤ 2 ^ 64) (hadd : add < 2 ^ 32) (hw : InRegions s.wr base n)
    (h3 : s.gpr .r3 = base + BitVec.ofNat 64 (n - 1)) (h4 : s.gpr .r4 = BitVec.ofNat 64 add)
    (h6 : s.gpr .r6 = BitVec.ofNat 64 n) :
    WP isa (.loop (.block addStep) (.nonzero .d .r6)) s fun t =>
      Spec.Rsa.bytesAt t.mem base n =
        Spec.Dsa.encodeBE n (Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem base n) + add) ∧
      Frame [⟨base, n⟩] s.mem t.mem ∧ Keep [.r3, .r4, .r5, .r6] s t ∧ t.sp = s.sp := by
  refine loop_nz (fun i t => ∃ c, AddInv s base n add i c t) hn
    (fun i hi t ⟨c, h⟩ => WP.mono (addBody_ok hn15 hfit hadd hw h hi) fun u ⟨hu, hz⟩ => ⟨⟨_, hu⟩, hz⟩)
    (fun t ⟨c, h⟩ => ?_) ⟨add, by omega_using [], by rw [h3, BitVec.add_zero], h4, Nat.le_refl _, by rw [h6, Nat.sub_zero],
      Frame.refl _ _, fun _ _ => rfl, ?_, Keep.refl _ _, rfl⟩
  · rw [Nat.sub_zero, List.take_of_length_le (by simp [Spec.Rsa.bytesAt])]
    simp [Spec.Rsa.bytesAt]
  · have e := h.enc
    rw [Nat.sub_self, VG.Proof.Dsa.Generation.seedAdd_nil, List.nil_append, BitVec.add_zero] at e
    exact ⟨e.symm, h.frame, h.keep, h.sp⟩

end VG.Proof.Dsa.PPC64LE.Gen

end

end


/-! # DSA parameter generation on PPC64LE: one hash of X

`pHash j` (`pHash_vp`): the seed copied to `sMsg`, `offset + j` added to it
(`seedAdd_vp`, big-endian modulo `2^(8 seedlen)`), and its hash into its
place in X.
-/

@[expose] public section

namespace VG.Proof.Dsa.PPC64LE.Gen
open VG VG.PPC64LE
open VG.Impl.Dsa.PPC64LE.Generation

section
variable {G : GP} {c : Cfg} {X : State → Prop}

/-- `seed + v` (big-endian, `seedlen` bytes). -/
abbrev seedPlus (G : GP) (sd : List Byte) (v : Nat) : List Byte := Spec.Dsa.encodeBE G.qLen (Spec.Dsa.decodeBE sd + v)

/-- `offset + j` added to the seed at `sMsg`. -/
theorem seedAdd_vp {j off : Nat} (hq : G.qLen = 20 ∨ G.qLen = 32)
    (hO : fOffset ∈ c.LS) (hOv : c.V fOffset = BitVec.ofNat 64 off) (hj : j < 2 ^ 15) (hoff : off + j < 2 ^ 32)
    {sd : List Byte} (hsd : (sMsg, sd) ∈ c.cl) (hsl : sd.length = G.qLen) {cl' : Claims}
    (hcl : ∀ x ∈ cl', x ∈ c.cl ∧ Apart sMsg G.qLen x) :
    VP (St G c X) (seedAdd G.qLen j)
      (St G { c with cl := (sMsg, seedPlus G sd (off + j)) :: cl' } X) := by
  unfold seedAdd
  obtain hq0 : 0 < G.qLen := by omega_using [hq]
  let M : State → State → Prop := fun σ s => St G c X σ s ∧ s.gpr .r3 = G.sa (sMsg + G.qLen - 1) ∧
    s.gpr .r4 = BitVec.ofNat 64 (off + j) ∧ s.gpr .r6 = BitVec.ofNat 64 G.qLen
  refine VP.seq (G := M) (VP.pub (SS.pub (c := fun _ => c) fun σ s h => h.1) []
    ⟨VG.Taint.hintOfSize VG.PPC64LE.taint 64 (Taint.ofRegs [.r28])
      (.block [scr .r3 (sMsg + G.qLen - 1), ld .r4 fOffset, .addi .r4 .r4 j, .li .r6 G.qLen]), rfl⟩
    (fun _ _ _ _ _ _ _ h => absurd h (by simp)) fun σ s ⟨h, x⟩ => ?_) ?_
  · refine WP.sp_eq ?_
    refine WP.wr (exec_addi (by decide) (by simp only [sMsg]; omega_using [hq])) fun s₁ u₁ sp₁ _ => ?_
    obtain h₁ := h.of_upd u₁ sp₁ (by decide)
    refine h₁.ldK (o := fOffset) (by decide) (by decide) ((h₁.gi.slotV hO).trans hOv) (by decide)
      fun s₂ h₂ u₂ => ?_
    refine WP.wr (exec_addi (by decide) hj) fun s₃ u₃ sp₃ _ => ?_
    obtain h₃ := h₂.of_upd u₃ sp₃ (by decide)
    refine WP.wr (exec_li (by omega_using [hq])) fun t u sp _ => WP.block_nil fun _ => ⟨⟨h₃.of_upd u sp (by decide), x⟩, ?_, ?_, ?_⟩
    · rw [u.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr, h.gi.r28]
    · rw [u.other _ (by decide), u₃.gpr, u₂.gpr, BitVec.ofNat_add]
    · rw [u.gpr]
  refine VP.pub (G := G) (fun σ s ⟨⟨h, _⟩, _⟩ => ⟨h.gi.r28, by rw [h.gi.sp, ← h.gi.hG]; rfl⟩) [.r3, .r4, .r6]
    ⟨VG.Taint.hintOfSize VG.PPC64LE.taint 64 (Taint.ofRegs [.r28, .r3, .r4, .r6])
      (.loop (.block addStep) (.nonzero .d .r6)), rfl⟩ (fun σ₁ σ₂ s₁ s₂ ⟨_, a3, a4, a6⟩ ⟨_, b3, b4, b6⟩ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · rw [a3, b3]
      · rw [a4, b4]
      · rw [a6, b6]) fun σ s ⟨⟨h, x⟩, r3, r4, r6⟩ => ?_
  have gi := h.gi
  have big := gi.wBig
  have fit := gi.scrFit
  have kb := gi.kBig
  have nM : sMsg = 512 := rfl
  have nE : hEnd = 352 := rfl
  obtain hkB : sMsg + 64 ≤ kB G.pLen := by rcases gi.lens3 with e | e | e <;> rw [e] <;> decide
  obtain hw : InRegions s.wr (G.sa sMsg) G.qLen := gi.inScr (by omega_using [hq, big, kb, hkB]) (by omega_using [hq])
  refine (addLoop_ok (base := G.sa sMsg) hq0 (by omega_using [hq]) (by
      have : kB G.pLen ≤ wB G.pLen := by simp only [wB]; omega_using []
      rw [GP.sa, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := sMsg) (by omega_using [nM]),
        Nat.mod_eq_of_lt (by omega_using [big, fit, kb, hkB])]; omega_using [hq, big, fit, kb, hkB]) hoff hw (by rw [r3, GP.sa_add]; congr 2; omega_using [hq]) r4 r6).mono fun t ⟨e, f, K, sp⟩ => ⟨?_, x⟩
  obtain b := h.sb (sMsg, sd) hsd
  rw [hsl] at b
  rw [b] at e
  refine h.of_scrs K sp (os := [(sMsg, G.qLen)]) (fun p hp => ?_) (f.mono fun r hr => List.mem_append_left _ (by
    simpa [GP.rss] using hr)) fun y hy => ?_
  · simp only [List.mem_singleton] at hp; subst hp; simp only [ClOk, List.length_replicate]; omega_using [hq, big, kb, nM, nE, hkB]
  rcases List.mem_cons.mp hy with rfl | hy
  · exact .inr ⟨by rw [VG.Proof.Dsa.encodeBE_length]; exact e,
      by simp only [ClOk, VG.Proof.Dsa.encodeBE_length]; omega_using [hq, big, kb, nM, nE, hkB]⟩
  · exact .inl ⟨(hcl y hy).1, fun p hp => by simp only [List.mem_singleton] at hp; subst hp; exact (hcl y hy).2⟩

/-- The block at `sMsg`: a message of `qLen` bytes and its padding. -/
theorem SS.blk_bytes {STK : Nat} {σ s : State} (h : SS G STK σ c s) {B N L : Nat} {md : MdStream.Md B N L}
    {m : List Byte} (hL : L = 8) (hq56 : G.qLen < 56) (hm : (sMsg, m) ∈ c.cl) (hml : m.length = G.qLen)
    (hpad : (sMsg + G.qLen, padTail md G.qLen) ∈ c.cl) :
    Spec.Rsa.bytesAt s.mem (G.sa sMsg) 64 = blk md m := by
  obtain b1 := h.sb _ hm
  obtain b2 := h.sb _ hpad
  obtain pl := padTail_length md hq56 hL
  rw [show (64 : Nat) = m.length + (padTail md G.qLen).length by omega_using [hq56, hml, pl], VG.Proof.Dsa.Generation.bytesAt_append,
    b1]
  obtain a : VG.Proof.Bignum.off (G.sa sMsg) m.length = G.sa (sMsg + G.qLen) := by
    rw [VG.Proof.Bignum.off, GP.sa_add, hml]
  rw [a]
  simp only at b2
  rw [b2]
  simp only [blk, padTail, hml, List.append_assoc]

/-- The hash of the seed at `k` plus `off + j`, to `dst`. -/
theorem pHash_vp {g : Geo} (HO : HashOk g.G) {j : Nat}
    (hlq : (G.pLen = 128 ∧ G.qLen = 20) ∨ (G.pLen = 256 ∧ G.qLen = 32) ∨ (G.pLen = 384 ∧ G.qLen = 32))
    (hp : g.pLen = G.pLen) (hq : g.qLen = G.qLen) (hk4 : 4 * g.G.k = G.qLen) (hsb : G.seedsB.length = G.seedsLen)
    {k off : Nat} (hk : k + G.qLen ≤ G.seedsLen) (hS : fSeed ∈ c.LS) (hSv : c.V fSeed = G.seeds + BitVec.ofNat 64 k)
    (hO : fOffset ∈ c.LS) (hOv : c.V fOffset = BitVec.ofNat 64 off) (hj : j < 2 ^ 15) (hoff : off + j < 2 ^ 32)
    (hd1 : sState + 32 ≤ sX + G.pLen - (j + 1) * G.qLen) (hd2 : sX + G.pLen - (j + 1) * G.qLen + 32 ≤ kB G.pLen)
    (hpad : (sMsg + G.qLen, padTail HO.md G.qLen) ∈ c.cl) {cl' : Claims}
    (hcl : ∀ x ∈ cl', x ∈ c.cl ∧ Apart sMsg 64 x ∧ Apart sState 32 x ∧ Apart (wB G.pLen) 1024 x ∧
      Apart (sX + G.pLen - (j + 1) * G.qLen) G.qLen x) :
    VP (St G c X) (g.pHash j)
      (St G { c with cl := (sMsg + G.qLen, padTail HO.md G.qLen) :: (sX + G.pLen - (j + 1) * G.qLen,
        HO.H (seedPlus G (seedAt G k) (off + j))) :: cl' } X) := by
  obtain hq0 : 0 < G.qLen := by omega_using [hlq]
  obtain hq56 : G.qLen < 56 := by omega_using [hlq]
  obtain pl := padTail_length HO.md hq56 HO.hL
  obtain hsl : (seedAt G k).length = G.qLen := by
    simp only [seedAt, List.length_take, List.length_drop, hsb]; omega_using [hk]
  obtain spl : (seedPlus G (seedAt G k) (off + j)).length = G.qLen := VG.Proof.Dsa.encodeBE_length _ _
  obtain hHl : (HO.H (seedPlus G (seedAt G k) (off + j))).length = G.qLen := by
    rw [HO.hash _ (by omega_using [hlq, spl]), HO.md.digest_length, HO.hN, hk4]
  obtain hkw : kB G.pLen ≤ wB G.pLen := by simp only [wB]; omega_using []
  obtain hkB : sMsg + 64 ≤ kB G.pLen := by rcases hlq with ⟨e, _⟩ | ⟨e, _⟩ | ⟨e, _⟩ <;> rw [e] <;> decide
  obtain hWW : 1024 ≤ 8 * wWords G.pLen := by rcases hlq with ⟨e, _⟩ | ⟨e, _⟩ | ⟨e, _⟩ <;> rw [e] <;> decide
  have nM : sMsg = 512 := rfl
  have nS : sState = 576 := rfl
  have nE : hEnd = 352 := rfl
  generalize hpd : padTail HO.md G.qLen = pad at hpad pl
  unfold Geo.pHash
  simp only [VG.Impl.Rsa.PPC64LE.Keys.seqs]
  rw [hq, hp]
  let c1 : Cfg := { c with cl := (sMsg, seedAt G k) :: (sMsg + G.qLen, pad) :: cl' }
  let c2 : Cfg := { c with cl := (sMsg, seedPlus G (seedAt G k) (off + j)) :: (sMsg + G.qLen, pad) :: cl' }
  refine VP.seq (G := St G c1 X) ?_ (VP.seq (G := St G c2 X) ?_ ?_)
  · -- The seed.
    refine copyIn_vp (c := fun _ => c) (fun σ s h => h.1) hq0 (by omega_using [hlq]) (by decide) (by decide) (by decide)
      (P := G.seeds + BitVec.ofNat 64 k) (fun σ s h => (h.1.gi.slotV hS).trans hSv)
      (fun σ s h => by have := h.1.gi.wBig; simp only [ClOk, List.length_replicate]; omega_using [hlq, hkw, hkB, nM, nE, this])
      (fun σ s h => h.1.gi.seedSrc hk hq0) fun σ s t ⟨h, x⟩ h' _ e => ⟨?_, x⟩
    rw [h.gi.seedBytes hk] at e
    refine (h'.addCl (o := sMsg) (bs := seedAt G k) (by rw [hsl]; exact e)
      (by have := h.gi.wBig; simp only [ClOk, hsl]; omega_using [hlq, hkw, hkB, nM, nE, this])).mono (fun o ho => ⟨ho, rfl⟩) (fun y hy => ?_)
      (fun j hj => ⟨hj, rfl⟩) (fun d hd => ⟨hd, rfl⟩)
    rcases List.mem_cons.mp hy with rfl | hy
    · exact List.mem_cons_self
    refine List.mem_cons_of_mem _ (List.mem_filter.mpr ?_)
    rcases List.mem_cons.mp hy with rfl | hy
    · exact ⟨hpad, by simp only [Apart, decide_eq_true_eq]; omega_using []⟩
    · obtain ⟨m, a, -⟩ := hcl y hy
      exact ⟨m, by simp only [Apart, decide_eq_true_eq] at a ⊢; omega_using [hlq, a]⟩
  · -- `offset + j`.
    exact seedAdd_vp (c := c1) (by omega_using [hlq]) hO hOv hj hoff (by simp [c1]) hsl fun y hy => by
      rcases List.mem_cons.mp hy with rfl | hy
      · exact ⟨by simp [c1], .inr (by omega_using [])⟩
      · obtain ⟨m, a, _⟩ := hcl y hy; exact ⟨by simp [c1, hy], by simp only [Apart] at a ⊢; omega_using [hlq, a]⟩
  · -- The hash.
    refine hash_vp HO (c := fun _ => c2) (fun σ s h => h.1) (msg := fun _ => seedPlus G (seedAt G k) (off + j))
      (dst := sX + G.pLen - (j + 1) * G.qLen) (fun σ s ⟨h, _⟩ => ⟨by omega_using [hlq, spl], ?_⟩) hd1 (by omega_using [hd2, hkw])
      fun σ s t ⟨h, x⟩ K sp f e => ⟨?_, x⟩
    · exact h.blk_bytes HO.hL hq56 (by simp [c2]) spl (by rw [hpd]; simp [c2])
    have big := h.gi.wBig
    refine h.of_scrs K sp (os := [(sState, 32), (wB G.pLen, 1024), (sX + G.pLen - (j + 1) * G.qLen, 4 * g.G.k)])
      (fun p hp => ?_) (f.mono fun r hr => List.mem_append_left _ hr) fun y hy => ?_
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl <;> simp only [ClOk, List.length_replicate, hk4] <;> omega_arith
    rcases List.mem_cons.mp hy with rfl | hy
    · refine .inl ⟨by simp [c2], fun p hp => ?_⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl <;> simp only [Apart, pl, hk4] <;> omega_arith
    rcases List.mem_cons.mp hy with rfl | hy
    · rw [hk4] at e
      exact .inr ⟨by rw [hHl]; exact e, by simp only [ClOk, hHl]; omega_using [hlq, hk4, hk, hj, hoff, hd1, hd2, hq0, hq56, hkw, hkB, hWW, nM, nS, nE, big]⟩
    · obtain ⟨m, a, b, d, d'⟩ := hcl y hy
      refine .inl ⟨by simp [c2, hy], fun p hp => ?_⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl <;> simp only [Apart, hk4] at a b d d' ⊢ <;> omega_arith

end

end VG.Proof.Dsa.PPC64LE.Gen

end

end


/-! # DSA parameter generation on PPC64LE: X

`pHashes m` (`pHashes_vp`): the first `m` hashes of X, each just below the
one before, in one claim (`accB`) whose value is the sum of the
contributions (`accB_value`); `pX` (`pX_vp`): X's top bit set.
-/

@[expose] public section

namespace VG.Proof.Dsa.PPC64LE.Gen
open VG VG.PPC64LE
open VG.Impl.Dsa.PPC64LE.Generation
open VG.Proof.Ffdh.ParameterCandidate (topCut topByte)
open VG.Proof.Dsa.Generation (contributions pDigest)

theorem bytesAt_length' (m : Mem) (p : Addr) (n : Nat) : (Spec.Rsa.bytesAt m p n).length = n := by
  simp [Spec.Rsa.bytesAt]

/-- A slice of bytes. -/
theorem bytesAt_slice' (m : Mem) (p : Addr) {k n len : Nat} (h : k + n ≤ len) :
    Spec.Rsa.bytesAt m (p + BitVec.ofNat 64 k) n = ((Spec.Rsa.bytesAt m p len).drop k).take n := by
  obtain ⟨r, rfl⟩ : ∃ r, len = k + (n + r) := ⟨len - k - n, by omega_using [h]⟩
  rw [VG.Proof.Dsa.Generation.bytesAt_append, VG.Proof.Dsa.Generation.bytesAt_append,
    List.drop_left' (bytesAt_length' _ _ _),
    List.take_left' (bytesAt_length' _ _ _)]

section
variable {G : GP} {Gh : Hash}

/-- Hash `j` of X, from the seed at `k` and the offset `off`. -/
abbrev hX (HO : HashOk Gh) (G : GP) (k off j : Nat) : List Byte := HO.H (seedPlus G (seedAt G k) (off + j))

/-- The first `m` hashes of X, the last first. -/
def accB (HO : HashOk Gh) (G : GP) (k off : Nat) : Nat → List Byte
  | 0 => []
  | m + 1 => hX HO G k off m ++ accB HO G k off m

/-- Where the first `m` hashes of X start. -/
abbrev pStart (G : GP) (m : Nat) : Nat := sX + G.pLen - m * G.qLen

theorem accB_length (HO : HashOk Gh) {k off : Nat} (hl : ∀ j, (hX HO G k off j).length = G.qLen) :
    ∀ m, (accB HO G k off m).length = m * G.qLen
  | 0 => by simp [accB]
  | m + 1 => by rw [accB, List.length_append, hl, accB_length HO hl m, Nat.succ_mul]; omega_using []

theorem accB_value (HO : HashOk Gh) {k off : Nat} (hl : ∀ j, (hX HO G k off j).length = G.qLen)
    (hH : ∀ m, HO.H m = Spec.Dsa.seedHash (8 * G.qLen) m) (hsl : (seedAt G k).length = G.qLen) :
    ∀ m, Spec.Dsa.decodeBE (accB HO G k off m) = contributions (8 * G.qLen) (pDigest (8 * G.qLen) (seedAt G k) off) m
  | 0 => rfl
  | m + 1 => by
    rw [accB, VG.Proof.Dsa.Generation.prepend_digest, accB_value HO hl hH hsl m,
      VG.Proof.Dsa.Generation.contributions_succ, accB_length HO hl m]
    congr 1
    rw [show (256 : Nat) = 2 ^ 8 from rfl, ← Nat.pow_mul, show 8 * (m * G.qLen) = m * (8 * G.qLen) by
      rw [Nat.mul_left_comm]]
    congr 1
    simp only [hX, hH, pDigest, seedPlus, hsl, Nat.add_assoc]

/-- Other claims, which the memory holds. -/
theorem SS.reclaim {STK : Nat} {σ s : State} {c : Cfg} (h : SS G STK σ c s) {cl' : Claims}
    (hcl : ∀ x ∈ cl', Spec.Rsa.bytesAt s.mem (G.sa x.1) x.2.length = x.2 ∧ ClOk G x) :
    SS G STK σ { c with cl := cl' } s :=
  ⟨h.gi, fun x hx => (hcl x hx).1, fun x hx => (hcl x hx).2, h.arrs, h.liveOk, h.ksl, h.kslOk⟩

/-- Two claims side by side, as one. -/
theorem SB.join {m : Mem} {cl : Claims} (h : SB G m cl) {o : Nat} {a b : List Byte} (ha : (o, a) ∈ cl)
    (hb : (o + a.length, b) ∈ cl) : Spec.Rsa.bytesAt m (G.sa o) (a ++ b).length = a ++ b := by
  rw [List.length_append, VG.Proof.Dsa.Generation.bytesAt_append, h _ ha]
  obtain e : VG.Proof.Bignum.off (G.sa o) a.length = G.sa (o + a.length) := by
    rw [VG.Proof.Bignum.off, GP.sa_add]
  rw [e, h _ hb]

/-- The claims during X. -/
abbrev pCfg (c : Cfg) (HO : HashOk Gh) (G : GP) (k off m : Nat) (rest : Claims) : Cfg :=
  { c with cl := (sMsg + G.qLen, padTail HO.md G.qLen) :: (pStart G m, accB HO G k off m) :: rest }

/-- The first `m` hashes of X. -/
theorem pHashes_vp {g : Geo} (HO : HashOk g.G) {c : Cfg} {X : State → Prop}
    (hlq : (G.pLen = 128 ∧ G.qLen = 20) ∨ (G.pLen = 256 ∧ G.qLen = 32) ∨ (G.pLen = 384 ∧ G.qLen = 32))
    (hp : g.pLen = G.pLen) (hq : g.qLen = G.qLen) (hk4 : 4 * g.G.k = G.qLen) (hsb : G.seedsB.length = G.seedsLen)
    {k off n : Nat} (hk : k + G.qLen ≤ G.seedsLen) (hS : fSeed ∈ c.LS) (hSv : c.V fSeed = G.seeds + BitVec.ofNat 64 k)
    (hO : fOffset ∈ c.LS) (hOv : c.V fOffset = BitVec.ofNat 64 off) (hn : n < 2 ^ 15) (hoff : off + n < 2 ^ 32)
    (hnq : n * G.qLen ≤ G.pLen + 64) {rest : Claims}
    (hrest : ∀ x ∈ rest, Apart sMsg 64 x ∧ Apart sState 32 x ∧ Apart (wB G.pLen) 1024 x ∧
      Apart (pStart G n) (n * G.qLen) x) :
    ∀ m ≤ n, VP (St G (pCfg c HO G k off 0 rest) X) (g.pHashes m) (St G (pCfg c HO G k off m rest) X)
  | 0, _ => VP.block_nil fun _ _ h => h
  | m + 1, hm => by
    obtain ih := pHashes_vp (X := X) HO hlq hp hq hk4 hsb hk hS hSv hO hOv hn hoff hnq hrest m (by omega_using [hm])
    refine VP.seq ih ?_
    have nX : sX = 672 := rfl
    have nS : sState = 576 := rfl
    have nM : sMsg = 512 := rfl
    have nE : hEnd = 352 := rfl
    obtain hkw : kB G.pLen ≤ wB G.pLen := by simp only [wB]; omega_using []
    obtain hkB : sX + G.pLen + 32 ≤ kB G.pLen := by rcases hlq with ⟨e, _⟩ | ⟨e, _⟩ | ⟨e, _⟩ <;> rw [e] <;> decide
    obtain hHl : ∀ j, (hX HO G k off j).length = G.qLen := fun j => by
      rw [hX, HO.hash _ (by rw [VG.Proof.Dsa.encodeBE_length]; omega_using [hlq]), HO.md.digest_length, HO.hN, hk4]
    obtain al := accB_length HO hHl m
    obtain hm1 : (m + 1) * G.qLen = m * G.qLen + G.qLen := Nat.succ_mul _ _
    obtain hmn : (m + 1) * G.qLen ≤ n * G.qLen := Nat.mul_le_mul_right _ hm
    obtain e1 : pStart G (m + 1) + G.qLen = pStart G m := by
      simp only [pStart]; omega_using [hnq, nX, hm1, hmn]
    refine (pHash_vp (c := pCfg c HO G k off m rest) (j := m) HO hlq hp hq hk4 hsb hk hS hSv hO hOv (by omega_using [hn, hm])
      (by omega_using [hoff, hm]) (by omega_using [hnq, nX, nS, hmn]) (by omega_using [hkB]) (by simp) (cl' := (pStart G m, accB HO G k off m) :: rest)
      fun x hx => ?_).mono (fun _ _ h => h) fun σ s ⟨h, x⟩ => ⟨h.reclaim fun y hy => ?_, x⟩
    · rcases List.mem_cons.mp hx with rfl | hx
      · refine ⟨by simp, ?_, ?_, ?_, ?_⟩ <;> simp only [Apart, al, pStart] <;> omega_arith
      · obtain ⟨a, b, d, d'⟩ := hrest x hx
        refine ⟨by simp [hx], a, b, d, ?_⟩
        simp only [Apart, pStart] at d' ⊢
        omega_using [hm1, hmn, d']
    · have sb := h.sb
      have cl := h.clOk
      simp only [List.mem_cons] at hy
      rcases hy with rfl | rfl | hy
      · exact ⟨sb _ (by simp), cl _ (by simp)⟩
      · have j := sb.join (o := pStart G (m + 1)) (a := hX HO G k off m) (b := accB HO G k off m)
          (by simp [pStart]) (by rw [hHl, e1]; simp)
        refine ⟨j, ?_⟩
        have big := h.gi.wBig
        show ClOk G (pStart G (m + 1), hX HO G k off m ++ accB HO G k off m)
        rw [ClOk, List.length_append, hHl, accB_length HO hHl]
        simp only [pStart]; omega_using [hlq, hk4, hk, hnq, hm, nX, nE, hkw, hkB, hm1, hmn, e1, big]
      · exact ⟨sb _ (by simp [hy]), cl _ (by simp [hy])⟩

theorem top_memory {m : Mem} {op : Addr} {n : Nat} (hn : 1 ≤ n) (hn64 : n < 2 ^ 64) :
    Spec.Rsa.bytesAt (m.writeW op (m op ||| 128#8)) op n = topCut (Spec.Rsa.bytesAt m op n) 7 := by
  obtain hne : Spec.Rsa.bytesAt m op n ≠ [] := by
    intro h; have := bytesAt_length' m op n; rw [h] at this; simp at this; omega_using [hn, this]
  apply List.ext_getElem
  · rw [bytesAt_length', VG.Proof.Ffdh.ParameterCandidate.topCut_length hne, bytesAt_length']
  · intro i hi hi'
    obtain hil : i < n := by simpa only [bytesAt_length'] using hi
    obtain hget : (topCut (Spec.Rsa.bytesAt m op n) 7)[i] = (topCut (Spec.Rsa.bytesAt m op n) 7).getD i 0 := by
      simp [List.getD_eq_getElem?_getD, hi']
    rw [hget, VG.Proof.Ffdh.ParameterCandidate.topCut_getD, VG.Proof.Dsa.Generation.topByte_seven]
    simp only [Spec.Rsa.bytesAt, List.getElem_map, List.getElem_range, VG.WriteBytes.writeW8_apply]
    by_cases hiz : i = 0
    · subst i; simp [show 0 < n by omega_using [hn]]
    · have hne0 : op + BitVec.ofNat 64 i ≠ op := by
        simpa using Offset.add_ofNat_ne op (by omega_using [hn64, hil] : i < 2 ^ 64) (by decide : 0 < 2 ^ 64) hiz
      simp [hiz, hne0, hil]

/-- X's top bit set. -/
theorem topX_vp {STK : Nat} {P Q : State → State → Prop} {c : State → Cfg} {N : Nat} {bs : List Byte}
    (hF : ∀ σ s, P σ s → SS G STK σ (c σ) s) (hN : 1 ≤ N) (hN' : sX + N ≤ kB G.pLen)
    (hb : ∀ σ s, P σ s → Spec.Rsa.bytesAt s.mem (G.sa sX) N = bs)
    (k : ∀ σ s t, P σ s → Keep [.r0] s t → t.sp = s.sp → Frame [G.rs sX N] s.mem t.mem →
      Spec.Rsa.bytesAt t.mem (G.sa sX) N = topCut bs 7 → Q σ t) :
    VP P (.block [.lbz .r0 .r28 sX, .ori .r0 .r0 0x80, .stb .r0 .r28 sX]) Q := by
  refine VP.pub (SS.pub hF) [] ⟨VG.Taint.hintOfSize VG.PPC64LE.taint 64 (Taint.ofRegs [.r28])
      (.block [.lbz .r0 .r28 sX, .ori .r0 .r0 0x80, .stb .r0 .r28 sX]), rfl⟩
    (fun _ _ _ _ _ _ _ h => absurd h (by simp)) fun σ s hs => ?_
  have h := hF σ s hs
  have gi := h.gi
  have big := gi.wBig
  have fit := gi.scrFit
  have kb := gi.kBig
  have hkw : kB G.pLen ≤ wB G.pLen := by simp only [wB]; omega_using []
  have nX : sX = 672 := rfl
  have kb15 : kB G.pLen < 2 ^ 15 := by rcases gi.lens3 with e | e | e <;> rw [e] <;> decide
  have c0 : (G.rs sX N).Contains (G.sa sX) (8 / 8) :=
    Offset.contains G.scr (d := sX) (n := 1) (e := sX) (k := N) (Nat.le_refl _) (by omega_using [hN]) (by omega_using [hN', kb15])
  have a0 : s.gpr .r28 + BitVec.ofNat 64 sX = G.sa sX := by rw [gi.r28]
  refine WP.sp_eq ?_
  refine wp_lbz (by decide) (by decide) a0 (gi.inRdWr (by omega_using [hN, hN', big, kb])) fun s₁ u₁ => ?_
  refine WP.wr exec_ori fun s₂ u₂ _ _ => ?_
  refine wp_stb (a := G.sa sX) (by decide) (by decide)
    (by rw [u₂.other _ (by decide), u₁.other _ (by decide)]; exact a0)
    (by rw [u₂.wr, u₁.wr]; exact gi.inScr (by omega_using [hN, hN', big, kb])) fun t m₃ => WP.block_nil fun sp => ?_
  have K : Keep [.r0] s t := ⟨fun r hr => by
      have hr : r ≠ .r0 := by simpa using hr
      rw [m₃.gpr, u₂.other _ hr, u₁.other _ hr], by rw [m₃.rd, u₂.rd, u₁.rd], by rw [m₃.wr, u₂.wr, u₁.wr]⟩
  have mt : t.mem = s.mem.writeW (G.sa sX) (s.mem (G.sa sX) ||| 128#8) := by
    rw [m₃.mem, u₂.gpr, u₁.gpr, u₂.mem, u₁.mem, or_byte]; rfl
  refine k σ s t hs K sp ?_ ?_
  · rw [mt]
    exact Frame.writeW (r := G.rs sX N) (w := 8) (Frame.refl _ _) List.mem_cons_self _ c0
  · rw [mt, top_memory hN (by omega_using [hN', kb15]), hb σ s hs]

/-- `(L − 1) / N`, the number of whole hashes below X's top one. -/
abbrev cnt (G : GP) : Nat := (8 * G.pLen - 1) / (8 * G.qLen)

/-- X's bytes: the low `pLen` bytes of the hashes, the top bit set. -/
abbrev xBytes (HO : HashOk Gh) (G : GP) (k off : Nat) : List Byte :=
  topCut ((accB HO G k off (cnt G + 1)).drop ((cnt G + 1) * G.qLen - G.pLen)) 7

theorem decodeBE_drop (bs : List Byte) (d : Nat) :
    Spec.Dsa.decodeBE (bs.drop d) = Spec.Dsa.decodeBE bs % 256 ^ (bs.length - d) := by
  obtain e := VG.Proof.Dsa.decodeBE_append (bs.take d) (bs.drop d)
  rw [List.take_append_drop, List.length_drop] at e
  rw [e, Nat.add_comm, Nat.add_mul_mod_self_right,
    Nat.mod_eq_of_lt (by have := VG.Proof.Dsa.decodeBE_lt (bs.drop d); rwa [List.length_drop] at this)]

/-- X's value. -/
theorem xBytes_value {A : List Byte} {d n : Nat} (hA : A.length = d + n) (hn : 1 ≤ n) :
    Spec.Dsa.decodeBE (topCut (A.drop d) 7) = Spec.Dsa.decodeBE A % 2 ^ (8 * n - 1) + 2 ^ (8 * n - 1) := by
  obtain hne : A.drop d ≠ [] := by
    intro h; have := congrArg List.length h; rw [List.length_drop] at this; simp at this; omega_using [hA, hn, this]
  rw [VG.Proof.Dsa.decodeBE_os2ip, VG.Proof.Ffdh.ParameterCandidate.topCut_value hne (by decide),
    ← VG.Proof.Dsa.decodeBE_os2ip, decodeBE_drop, List.length_drop, hA,
    show d + n - d = n by omega_using [], show 8 * (n - 1) + 7 = 8 * n - 1 by omega_using [hn],
    show (256 : Nat) ^ n = 2 ^ (8 * n) by rw [Nat.pow_mul],
    Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 (by omega_using []))]

/-- The candidate p of the spec, from X's value. -/
theorem pCandidate_xBytes (HO : HashOk Gh) {k off : Nat} (hl : ∀ j, (hX HO G k off j).length = G.qLen)
    (hH : ∀ m, HO.H m = Spec.Dsa.seedHash (8 * G.qLen) m) (hsl : (seedAt G k).length = G.qLen)
    (hlen : ∀ bs, 8 * (Spec.Dsa.seedHash (8 * G.qLen) bs).length = 8 * G.qLen)
    (hp1 : 1 ≤ G.pLen) (hc : G.pLen ≤ (cnt G + 1) * G.qLen) (q : Nat) :
    Spec.Dsa.pCandidate (8 * G.pLen) (8 * G.qLen) q (seedAt G k) off =
      Spec.Dsa.decodeBE (xBytes HO G k off) + 1 - Spec.Dsa.decodeBE (xBytes HO G k off) % (2 * q) := by
  rw [VG.Proof.Dsa.Generation.pCandidate_shaped (by omega_using [hp1]) hlen,
    VG.Proof.Ffdh.ParameterCandidate.candidate_low_high (by omega_using [hp1]),
    VG.Proof.Dsa.Generation.pReduction_orOne, xBytes,
    xBytes_value (by rw [accB_length HO hl]; omega_using [hc]) hp1, accB_value HO hl hH hsl]

/-- X, from the seed at `k` and the offset `off`, at `sX`. -/
theorem pX_vp {g : Geo} (HO : HashOk g.G) {c : Cfg} {X : State → Prop}
    (hlq : (G.pLen = 128 ∧ G.qLen = 20) ∨ (G.pLen = 256 ∧ G.qLen = 32) ∨ (G.pLen = 384 ∧ G.qLen = 32))
    (hp : g.pLen = G.pLen) (hq : g.qLen = G.qLen) (hk4 : 4 * g.G.k = G.qLen) (hsb : G.seedsB.length = G.seedsLen)
    {k off : Nat} (hk : k + G.qLen ≤ G.seedsLen) (hS : fSeed ∈ c.LS) (hSv : c.V fSeed = G.seeds + BitVec.ofNat 64 k)
    (hO : fOffset ∈ c.LS) (hOv : c.V fOffset = BitVec.ofNat 64 off) (hoff : off + (cnt G + 1) < 2 ^ 32)
    {rest : Claims}
    (hrest : ∀ x ∈ rest, Apart sMsg 64 x ∧ Apart sState 32 x ∧ Apart (wB G.pLen) 1024 x ∧
      Apart (pStart G (cnt G + 1)) ((cnt G + 1) * G.qLen) x) :
    VP (St G (pCfg c HO G k off 0 rest) X) g.pX
      (St G { c with cl := (sMsg + G.qLen, padTail HO.md G.qLen) :: (sX, xBytes HO G k off) :: rest } X) := by
  obtain hc : (cnt G + 1) * G.qLen ≤ G.pLen + 64 ∧ G.pLen ≤ (cnt G + 1) * G.qLen ∧ cnt G + 1 < 2 ^ 15 := by
    rcases hlq with ⟨e1, e2⟩ | ⟨e1, e2⟩ | ⟨e1, e2⟩ <;> simp only [cnt, e1, e2] <;> decide
  obtain hcount : g.count = cnt G := by simp only [Geo.count, hp, hq]
  have nX : sX = 672 := rfl
  have nE : hEnd = 352 := rfl
  have nM : sMsg = 512 := rfl
  obtain hq56 : G.qLen < 56 := by omega_using [hlq]
  obtain hkB : sX + G.pLen + 32 ≤ kB G.pLen := by rcases hlq with ⟨e, _⟩ | ⟨e, _⟩ | ⟨e, _⟩ <;> rw [e] <;> decide
  obtain hHl : ∀ j, (hX HO G k off j).length = G.qLen := fun j => by
    rw [hX, HO.hash _ (by rw [VG.Proof.Dsa.encodeBE_length]; omega_using [hlq]), HO.md.digest_length, HO.hN, hk4]
  obtain al := accB_length HO hHl (cnt G + 1)
  obtain hd : pStart G (cnt G + 1) + ((cnt G + 1) * G.qLen - G.pLen) = sX := by simp only [pStart]; omega_using [hc, nX]
  unfold Geo.pX
  rw [hcount]
  refine VP.seq (pHashes_vp HO hlq hp hq hk4 hsb hk hS hSv hO hOv hc.2.2 (by omega_using [hoff]) hc.1 hrest _ (Nat.le_refl _)) ?_
  refine topX_vp (c := fun _ => pCfg c HO G k off (cnt G + 1) rest) (fun σ s h => h.1) (N := G.pLen)
    (by omega_using [hlq]) (by omega_using [hkB]) (bs := (accB HO G k off (cnt G + 1)).drop ((cnt G + 1) * G.qLen - G.pLen))
    (fun σ s ⟨h, _⟩ => ?_) fun σ s t ⟨h, x⟩ K sp f e => ⟨?_, x⟩
  · have b := h.sb (pStart G (cnt G + 1), accB HO G k off (cnt G + 1)) (by simp)
    simp only at b
    rw [al] at b
    obtain a : G.sa sX = G.sa (pStart G (cnt G + 1)) + BitVec.ofNat 64 ((cnt G + 1) * G.qLen - G.pLen) := by
      rw [GP.sa_add, hd]
    rw [a, bytesAt_slice' _ _ (len := (cnt G + 1) * G.qLen) (by omega_using [hc]), b, List.take_of_length_le (by
      rw [List.length_drop, al]; omega_using [])]
  have big := h.gi.wBig
  obtain hkw : kB G.pLen ≤ wB G.pLen := by simp only [wB]; omega_using []
  refine h.of_scrs K sp (os := [(sX, G.pLen)]) (fun p hp => ?_) (f.mono fun r hr => List.mem_append_left _ (by
    simpa [GP.rss] using hr)) fun y hy => ?_
  · simp only [List.mem_singleton] at hp; subst hp; simp only [ClOk, List.length_replicate]; omega_using [nX, nE, hkB, big, hkw]
  rcases List.mem_cons.mp hy with rfl | hy
  · refine .inl ⟨by simp, fun p hp => ?_⟩
    simp only [List.mem_singleton] at hp; subst hp
    simp only [Apart, padTail_length HO.md (show G.qLen < 56 by omega_using [hlq]) HO.hL]; omega_using [hlq, nX, nM]
  rcases List.mem_cons.mp hy with rfl | hy
  · have hl : (xBytes HO G k off).length = G.pLen := by
      rw [xBytes, VG.Proof.Ffdh.ParameterCandidate.topCut_length (by
        rw [← List.length_pos_iff, List.length_drop, al]; omega_using [hlq, hc]), List.length_drop, al]; omega_using [hc]
    exact .inr ⟨by rw [hl]; exact e, by simp only [ClOk, hl]; omega_using [nX, nE, hkB, big, hkw]⟩
  · obtain ⟨_, _, _, d⟩ := hrest y hy
    refine .inl ⟨by simp [hy], fun p hp => ?_⟩
    simp only [List.mem_singleton] at hp; subst hp
    simp only [Apart, pStart] at d ⊢; omega_using [hc, d]

end

end VG.Proof.Dsa.PPC64LE.Gen
