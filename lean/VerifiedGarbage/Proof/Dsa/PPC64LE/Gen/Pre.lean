module

public import VerifiedGarbage.Proof.Dsa.PPC64LE.Gen.QPart
public import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.PPC64LE.ByteStep
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega

/-! # DSA parameter generation on PPC64LE: before the seeds

`pre_vp`: the last 64 − `qLen` bytes of a hash block after a `qLen`-byte
message (`padInit`), which every seed's hashes share: the search's first
stage.
-/

@[expose] public section

namespace VG.Proof.Dsa.PPC64LE.Gen
open VG VG.PPC64LE VG.WriteBytes
open VG.Impl.Dsa.PPC64LE.Generation

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

/-- The doublewords at `o + 8 i` of `r28`, for `i < k`, := `r0` (0): `8 k` zero bytes. -/
theorem zeros_ok {s : State} {a : Addr} {o : Nat} (r0 : s.gpr .r0 = 0) (ho : o + 64 < 2 ^ 15) (h4 : o % 8 = 0)
    (ha : ∀ i < 8, s.gpr .r28 + BitVec.ofNat 64 (o + 8 * i) = a + BitVec.ofNat 64 (8 * i))
    (hw : ∀ i < 8, InRegions s.wr (a + BitVec.ofNat 64 (8 * i)) 8) :
    ∀ k ≤ 8, ∀ {rest : List Instr} {Q : State → Prop},
      (∀ t, t.gpr = s.gpr → t.rd = s.rd → t.wr = s.wr → t.sp = s.sp → t.lr = s.lr →
        t.mem = writeBytes s.mem a (List.replicate (8 * k) 0) → WP isa (.block rest) t Q) →
      WP isa (.block (((List.range k).map fun i => st .r0 (o + 8 * i)) ++ rest)) s Q
  | 0, _, rest, Q, k => k s rfl rfl rfl rfl rfl (by simp [writeBytes_nil])
  | j + 1, hj, rest, Q, k => by
    rw [List.range_succ, List.map_append, List.append_assoc]
    refine zeros_ok r0 ho h4 ha hw j (by omega) fun t g rd wr sp lr m => ?_
    simp only [List.map_cons, List.map_nil, List.cons_append, List.nil_append]
    refine wp_std' (a := a + BitVec.ofNat 64 (8 * j)) (by decide) ⟨by omega, by omega⟩
      (by rw [g]; exact ha j (by omega)) (by rw [wr]; exact hw j (by omega)) fun t' u sp' lr' => ?_
    refine k t' (by rw [u.gpr, g]) (by rw [u.rd, rd]) (by rw [u.wr, wr]) (by rw [sp', sp]) (by rw [lr', lr]) ?_
    rw [u.mem, m, g, r0]
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

/-- The search's first stage: the end of a hash block. -/
theorem pre_vp {V : Nat → BitVec 64} {LS : List Nat} {B N L : Nat} (md : MdStream.Md B N L) (hL : L = 8)
    (hlq : (G.pLen = 128 ∧ G.qLen = 20) ∨ (G.pLen = 256 ∧ G.qLen = 32) ∨ (G.pLen = 384 ∧ G.qLen = 32))
    (hlb : md.lenBytes G.qLen =
      [0, 0, 0, 0, 0, 0, BitVec.ofNat 8 (8 * G.qLen / 256), BitVec.ofNat 8 (8 * G.qLen % 256)]) :
    VP (fun σ s => GI G 176 σ V LS s ∧ X σ) (.block (padInit G.qLen))
      (St G { V := V, LS := LS, cl := [(sMsg + G.qLen, padTail md G.qLen)] } X) := by
  refine VP.pub (G := G) (fun σ s h => ⟨h.1.r28, by rw [h.1.sp, ← h.1.hG]; rfl⟩) []
    ⟨VG.Taint.hintOfSize VG.PPC64LE.taint 64 (Taint.ofRegs [.r28]) (.block (padInit G.qLen)), rfl⟩
    (fun _ _ _ _ _ _ _ h => absurd h (by simp)) fun σ s ⟨gi, x⟩ => ?_
  have big := gi.scrBig
  have fit := gi.scrFit
  have hn : G.qLen = 20 ∨ G.qLen = 32 := by omega
  have hq32 : G.qLen ≤ 32 := by omega
  have nM : sMsg = 512 := rfl
  have hE : hEnd = 296 := rfl
  have kb : 576 ≤ kB G.pLen := by rcases hlq with ⟨e, _⟩ | ⟨e, _⟩ | ⟨e, _⟩ <;> rw [e] <;> decide
  have kz := gi.kBig
  have wb := gi.wBig
  have w : ∀ {o n : Nat}, 0 < n → o + n ≤ G.scrLen * 8 → InRegions s.wr (G.sa o) n := fun hn h => gi.inScr h hn
  simp only [padInit, List.cons_append, List.nil_append]
  refine WP.sp_eq ?_
  refine WP.wr (exec_li (show 0 < 2 ^ 15 by decide)) fun s₁ u₁ sp₁ lr₁ => ?_
  have hs : ∀ i < 8, s₁.gpr .r28 + BitVec.ofNat 64 (sMsg + 8 * i) = G.sa sMsg + BitVec.ofNat 64 (8 * i) :=
    fun i _ => by rw [u₁.other _ (by decide), gi.r28, GP.sa_add]
  refine zeros_ok (o := sMsg) (by rw [u₁.gpr]; rfl) (by decide) (by decide) hs
    (fun i hi => by rw [u₁.wr, GP.sa_add]; exact w (by decide) (by omega)) 8 (Nat.le_refl _) fun s₂ g₂ rd₂ wr₂ sp₂ lr₂ m₂ => ?_
  refine WP.wr (exec_li (show 0x80 < 2 ^ 15 by decide)) fun s₃ u₃ sp₃ lr₃ => ?_
  have a28 : ∀ {t : State} (o : Nat), t.gpr .r28 = s.gpr .r28 → t.gpr .r28 + BitVec.ofNat 64 o = G.sa o :=
    fun o e => by rw [e, gi.r28]
  have e28 : ∀ {t : State}, t.gpr .r28 = s₂.gpr .r28 → t.gpr .r28 = s.gpr .r28 :=
    fun e => by rw [e, g₂, u₁.other _ (by decide)]
  refine wp_stb (a := G.sa (sMsg + G.qLen)) (by decide) (by omega) (a28 _ (e28 (u₃.other _ (by decide))))
    (by rw [u₃.wr, wr₂, u₁.wr]; exact w (by decide) (by omega)) fun s₄ m₄ => ?_
  refine WP.wr (exec_li (show 8 * G.qLen / 256 < 2 ^ 15 by omega)) fun s₅ u₅ sp₅ lr₅ => ?_
  refine wp_stb (a := G.sa (sMsg + 62)) (by decide) (by decide)
    (a28 _ (e28 (by rw [u₅.other _ (by decide), m₄.gpr, u₃.other _ (by decide)])))
    (by rw [u₅.wr, m₄.wr, u₃.wr, wr₂, u₁.wr]; exact w (by decide) (by omega)) fun s₆ m₆ => ?_
  refine WP.wr (exec_li (show 8 * G.qLen % 256 < 2 ^ 15 by omega)) fun s₇ u₇ sp₇ lr₇ => ?_
  refine wp_stb (a := G.sa (sMsg + 63)) (by decide) (by decide)
    (a28 _ (e28 (by rw [u₇.other _ (by decide), m₆.gpr, u₅.other _ (by decide), m₄.gpr, u₃.other _ (by decide)])))
    (by rw [u₇.wr, m₆.wr, u₅.wr, m₄.wr, u₃.wr, wr₂, u₁.wr]; exact w (by decide) (by omega)) fun t m₈ => WP.block_nil fun sp => ?_
  have sw8 : ∀ x : Nat, (BitVec.ofNat 64 x).setWidth 8 = BitVec.ofNat 8 x := fun x => by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    exact Nat.mod_mod_of_dvd _ (by decide)
  have hl64 : (List.replicate 64 (0 : Byte)).length < 2 ^ 64 := by simp
  have mt : t.mem = writeBytes s.mem (G.sa sMsg) (padList G.qLen) := by
    rw [m₈.mem, u₇.gpr, u₇.mem, m₆.mem, u₅.gpr, u₅.mem, m₄.mem, u₃.gpr, u₃.mem, m₂, u₁.mem]
    simp only [sw8]
    rw [← GP.sa_add, ← GP.sa_add, ← GP.sa_add]
    rw [writeBytes_set _ _ _ (by simp; omega) hl64, writeBytes_set _ _ _ (by simp) (by simp),
      writeBytes_set _ _ _ (by simp) (by simp)]
    rfl
  have K : Keep [.r0] s t := ⟨fun r hr => by
      have hr : r ≠ .r0 := by simpa using hr
      rw [m₈.gpr, u₇.other _ hr, m₆.gpr, u₅.other _ hr, m₄.gpr, u₃.other _ hr, g₂, u₁.other _ hr],
    by rw [m₈.rd, u₇.rd, m₆.rd, u₅.rd, m₄.rd, u₃.rd, rd₂, u₁.rd], by rw [m₈.wr, u₇.wr, m₆.wr, u₅.wr, m₄.wr, u₃.wr, wr₂, u₁.wr]⟩
  have f : Frame [G.rs sMsg 64, rBelow σ 176] s.mem t.mem := by
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

end VG.Proof.Dsa.PPC64LE.Gen
