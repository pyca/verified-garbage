module

public import VerifiedGarbage.Proof.Dsa.RISCV64.PSearch.Bytes
public import VerifiedGarbage.Proof.MdStream.Spec
public import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.KernelRfl

-- separate module: the search's first stage (`pre_vp`), which the controller's proof imports beside `Add`

/-! # DSA parameter search on RISC-V: before the seeds

As on PPC64LE (`Proof/Dsa/PPC64LE/Gen/Pre.lean`). `pre_vp`: the last
64 − `qLen` bytes of a hash block after a `qLen`-byte message (`padInit`),
which every seed's hashes share: the search's first stage.
-/

@[expose] public section

namespace VG.Proof.Dsa.RISCV64.PSearch
open VG VG.RISCV64 VG.RISCV64.Steps VG.WriteBytes
open VG.Impl.Dsa.RISCV64.ParameterSearch

/-- The padding of a block after a message of `n < 56` bytes. -/
def padTail {B N L : Nat} (md : MdStream.Md B N L) (n : Nat) : List Byte :=
  [0x80] ++ List.replicate (55 - n) 0 ++ md.lenBytes n

theorem padTail_length {B N L : Nat} (md : MdStream.Md B N L) {n : Nat} (hn : n < 56) (hL : L = 8) :
    (padTail md n).length = 64 - n := by
  simp only [padTail, List.length_append, List.length_cons, List.length_nil, List.length_replicate,
    md.lenBytes_length]
  omega

/-- A byte into bytes written before. -/
theorem writeBytes_set (m : Mem) (q : Addr) (xs : List Byte) {j : Nat} (hj : j < xs.length)
    (hl : xs.length < 2 ^ 64) (b : Byte) :
    (writeBytes m q xs).writeW (q + BitVec.ofNat 64 j) b = writeBytes m q (xs.set j b) := by
  funext x
  rw [writeW8_apply]
  simp only [writeBytes, List.length_set]
  by_cases hx : x = q + BitVec.ofNat 64 j
  · subst hx
    rw [Offset.add_sub_cancel_left, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    simp [hj, List.getD_eq_getElem?_getD]
  · have hne : (x - q).toNat ≠ j := by
      intro h'
      apply hx
      have : x - q = BitVec.ofNat 64 j := BitVec.eq_of_toNat_eq (by rw [h', BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)])
      rw [← BitVec.sub_add_cancel x q, this, BitVec.add_comm]
    simp only [hx, ite_false]
    split
    · simp only [List.getD_eq_getElem?_getD, List.getElem?_set_ne (Ne.symm hne)]
    · rfl

/-- Bytes within bytes written before. -/
theorem bytesAt_writeBytes (m : Mem) (q : Addr) (xs : List Byte) {d k : Nat} (h : d + k ≤ xs.length)
    (hl : xs.length < 2 ^ 64) :
    Spec.Rsa.bytesAt (writeBytes m q xs) (q + BitVec.ofNat 64 d) k = (xs.drop d).take k := by
  apply List.ext_getElem
  · simp [Spec.Rsa.bytesAt]; omega
  · intro i h1 h2
    simp only [Spec.Rsa.bytesAt, List.getElem_map, List.getElem_range, writeBytes, List.getElem_take,
      List.getElem_drop]
    rw [BitVec.add_assoc, Offset.add_sub_cancel_left, ← BitVec.ofNat_add, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by simp [Spec.Rsa.bytesAt] at h1; omega)]
    simp only [Spec.Rsa.bytesAt, List.length_map, List.length_range] at h1
    simp [show d + i < xs.length by omega, List.getD_eq_getElem?_getD]

/-- The doublewords at `o + 8 i` of `s6`, for `i < k`, := `t2` (0): `8 k` zero bytes. -/
theorem zeros_ok {s : State} {a : Addr} {o : Nat} (t2 : s.gpr .t2 = 0) (ho : o + 64 < 2048)
    (ha : ∀ i < 8, s.gpr .s6 + BitVec.ofNat 64 (o + 8 * i) = a + BitVec.ofNat 64 (8 * i))
    (hal : ∀ i < 8, (a + BitVec.ofNat 64 (8 * i)).toNat % 8 = 0)
    (hw : ∀ i < 8, InRegions s.wr (a + BitVec.ofNat 64 (8 * i)) 8) :
    ∀ k ≤ 8, ∀ {rest : List Instr} {Q : State → Prop},
      (∀ t, t.gpr = s.gpr → t.rd = s.rd → t.wr = s.wr → t.sp = s.sp →
        t.mem = writeBytes s.mem a (List.replicate (8 * k) 0) → WP isa (.block rest) t Q) →
      WP isa (.block (((List.range k).map fun i => st .t2 (o + 8 * i)) ++ rest)) s Q
  | 0, _, rest, Q, k => k s rfl rfl rfl rfl (by simp [writeBytes_nil])
  | j + 1, hj, rest, Q, k => by
    rw [List.range_succ, List.map_append, List.append_assoc]
    refine zeros_ok t2 ho ha hal hw j (by omega) fun t g rd wr sp m => ?_
    simp only [List.map_cons, List.map_nil, List.cons_append, List.nil_append]
    refine wp_sd (a := a + BitVec.ofNat 64 (8 * j)) (by omega)
      (by rw [g]; exact ha j (by omega)) (hal j (by omega)) (by rw [wr]; exact hw j (by omega)) fun t' u => ?_
    refine k t' (by rw [u.gpr, g]) (by rw [u.rd, rd]) (by rw [u.wr, wr]) (by rw [u.sp, sp]) ?_
    rw [u.mem, m, g, t2]
    show Mem.write (writeBytes s.mem a (List.replicate (8 * j) 0)) (a + BitVec.ofNat 64 (8 * j)) 8
      ((0 : BitVec 64).setWidth (8 * 8)) = _
    rw [write_eq_writeBytes]
    have z8 : ((List.range 8).map fun i => ((0 : BitVec 64).setWidth (8 * 8)).extractLsb' (8 * i) 8) =
        List.replicate 8 (0 : Byte) := by decide
    have ap := writeBytes_append s.mem a (List.replicate (8 * j) (0 : Byte)) (List.replicate 8 0) (by simp; omega)
    rw [List.length_replicate] at ap
    rw [z8, ap, List.replicate_append_replicate, Nat.mul_succ]

section
variable {G : GP} {X : State → Prop}

/-- The 64 bytes `padInit` leaves at `sMsg`. -/
abbrev padList (n : Nat) : List Byte :=
  (((List.replicate 64 (0 : Byte)).set n 0x80).set 62 (BitVec.ofNat 8 (8 * n / 256))).set 63
    (BitVec.ofNat 8 (8 * n % 256))

theorem padList_tail {B N L : Nat} (md : MdStream.Md B N L) {n : Nat} (hn : n = 20 ∨ n = 32)
    (hlb : md.lenBytes n = [0, 0, 0, 0, 0, 0, BitVec.ofNat 8 (8 * n / 256), BitVec.ofNat 8 (8 * n % 256)]) :
    ((padList n).drop n).take (64 - n) = padTail md n := by
  rw [padTail, hlb]; rcases hn with rfl | rfl <;> decide

theorem sw8 (x : Nat) : (BitVec.ofNat 64 x).setWidth 8 = BitVec.ofNat 8 x := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  exact Nat.mod_mod_of_dvd _ (by decide)

/-- The search's first stage: the end of a hash block. -/
theorem pre_vp {V : Nat → BitVec 64} {LS : List Nat} {B N L : Nat} (md : MdStream.Md B N L) (hL : L = 8)
    (hlb : md.lenBytes G.qLen =
      [0, 0, 0, 0, 0, 0, BitVec.ofNat 8 (8 * G.qLen / 256), BitVec.ofNat 8 (8 * G.qLen % 256)]) :
    VP (fun σ s => GI G STK0 σ V LS s ∧ X σ) (.block (padInit G.qLen))
      (St G { V := V, LS := LS, cl := [(sMsg + G.qLen, padTail md G.qLen)] } X) := by
  refine VP.pub (G := G) (fun σ s h => ⟨h.1.s6, by rw [h.1.sp, ← h.1.hG]; rfl⟩) []
    ⟨VG.Taint.hintOfSize VG.RISCV64.taint 64 (Taint.ofRegs [.s6]) (.block (padInit G.qLen)), by kernel_rfl⟩
    (fun _ _ _ _ _ _ _ h => absurd h (by simp)) fun σ s ⟨gi, x⟩ => ?_
  have big := gi.scrBig
  have fit := gi.scrFit
  have lens := gi.lens
  have hn : G.qLen = 20 ∨ G.qLen = 32 := by
    simp only [GP.qLen, Spec.Dsa.generationQLen]; split <;> simp
  have nM : sMsg = 320 := rfl
  have hE : hEnd = 280 := rfl
  have kb : 384 ≤ kB G.pLen := by rcases lens with e | e | e <;> rw [e] <;> decide
  have w : ∀ {o n : Nat}, 0 < n → o + n ≤ G.scrLen * 8 → InRegions s.wr (G.sa o) n := fun hn h => gi.inScr h hn
  simp only [padInit, List.cons_append, List.nil_append]
  refine wp_li (imm := 0) (by decide) fun s₁ u₁ => ?_
  have hs : ∀ i < 8, s₁.gpr .s6 + BitVec.ofNat 64 (sMsg + 8 * i) = G.sa sMsg + BitVec.ofNat 64 (8 * i) :=
    fun i _ => by rw [u₁.other _ (by decide), gi.s6, GP.sa_add]
  refine zeros_ok (o := sMsg) (by rw [u₁.gpr]; rfl) (by decide) hs
    (fun i hi => by rw [GP.sa_add]; exact gi.al8 (by omega) (by omega))
    (fun i hi => by rw [u₁.wr, GP.sa_add]; exact w (by decide) (by omega)) 8 (Nat.le_refl _)
    fun s₂ g₂ rd₂ wr₂ sp₂ m₂ => ?_
  have e6 : ∀ {t : State}, t.gpr .s6 = s₂.gpr .s6 → t.gpr .s6 = G.scr :=
    fun e => by rw [e, g₂, u₁.other _ (by decide), gi.s6]
  refine wp_li (imm := 0x80) (by decide) fun s₃ u₃ => ?_
  refine wp_sb (a := G.sa (sMsg + G.qLen)) (by omega) (by rw [e6 (u₃.other _ (by decide))])
    (by rw [u₃.wr, wr₂, u₁.wr]; exact w (by decide) (by omega)) fun s₄ m₄ => ?_
  refine wp_li (imm := 8 * G.qLen / 256) (by omega) fun s₅ u₅ => ?_
  refine wp_sb (a := G.sa (sMsg + 62)) (by decide)
    (by rw [e6 (by rw [u₅.other _ (by decide), m₄.gpr, u₃.other _ (by decide)])])
    (by rw [u₅.wr, m₄.wr, u₃.wr, wr₂, u₁.wr]; exact w (by decide) (by omega)) fun s₆ m₆ => ?_
  refine wp_li (imm := 8 * G.qLen % 256) (by omega) fun s₇ u₇ => ?_
  refine wp_sb (a := G.sa (sMsg + 63)) (by decide)
    (by rw [e6 (by rw [u₇.other _ (by decide), m₆.gpr, u₅.other _ (by decide), m₄.gpr, u₃.other _ (by decide)])])
    (by rw [u₇.wr, m₆.wr, u₅.wr, m₄.wr, u₃.wr, wr₂, u₁.wr]; exact w (by decide) (by omega)) fun t m₈ =>
      WP.block_nil ?_
  have hl64 : (List.replicate 64 (0 : Byte)).length < 2 ^ 64 := by simp
  have mt : t.mem = writeBytes s.mem (G.sa sMsg) (padList G.qLen) := by
    rw [m₈.mem, u₇.gpr, u₇.mem, m₆.mem, u₅.gpr, u₅.mem, m₄.mem, u₃.gpr, u₃.mem, m₂, u₁.mem]
    simp only [sw8]
    rw [← GP.sa_add, ← GP.sa_add, ← GP.sa_add]
    rw [writeBytes_set _ _ _ (by simp; omega) hl64, writeBytes_set _ _ _ (by simp) (by simp),
      writeBytes_set _ _ _ (by simp) (by simp)]
    rfl
  have K : Keep [.t2] s t := ⟨fun r hr => by
      have hr : r ≠ .t2 := by simpa using hr
      rw [m₈.gpr, u₇.other _ hr, m₆.gpr, u₅.other _ hr, m₄.gpr, u₃.other _ hr, g₂, u₁.other _ hr],
    by rw [m₈.rd, u₇.rd, m₆.rd, u₅.rd, m₄.rd, u₃.rd, rd₂, u₁.rd], by rw [m₈.wr, u₇.wr, m₆.wr, u₅.wr, m₄.wr, u₃.wr, wr₂, u₁.wr]⟩
  have sp : t.sp = s.sp := by rw [m₈.sp, u₇.sp, m₆.sp, u₅.sp, m₄.sp, u₃.sp, sp₂, u₁.sp]
  have f : Frame [G.rs sMsg 64, rBelow σ STK0] s.mem t.mem := by
    rw [mt]
    refine (writeBytes_frame _ _ _ (R := G.rs sMsg 64) ?_).mono (by simp)
    simp only [List.length_set, List.length_replicate]
    exact Region.contains_self _ _
  have pl := padTail_length md (n := G.qLen) (by omega) hL
  refine ⟨⟨gi.of_scr K sp (by omega) (by omega) f, fun y hy => ?_, fun y hy => ?_, fun j hj => absurd hj (by simp),
    fun j hj => absurd hj (by simp), fun d hd => absurd hd (by simp), fun d hd => absurd hd (by simp)⟩, x⟩
  · simp only [List.mem_singleton] at hy; subst hy
    show Spec.Rsa.bytesAt t.mem (G.sa (sMsg + G.qLen)) (padTail md G.qLen).length = _
    rw [mt, pl, ← GP.sa_add, bytesAt_writeBytes _ _ _ (by simp; omega) (by simp), padList_tail md hn hlb]
  · simp only [List.mem_singleton] at hy; subst hy
    refine ⟨by show hEnd ≤ sMsg + G.qLen; omega, .inl ?_, ?_⟩ <;>
      show sMsg + G.qLen + (padTail md G.qLen).length ≤ _ <;> rw [pl] <;> omega

end

end VG.Proof.Dsa.RISCV64.PSearch
