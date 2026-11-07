module

public import VerifiedGarbage.Proof.Modes.RISCV64.Seq
public import VerifiedGarbage.Impl.Modes.RISCV64.SeqFinal
public import VerifiedGarbage.Spec.Cfb.Final
public import VerifiedGarbage.Spec.Ofb.Final
import VerifiedGarbage.Proof.Modes.FbFinal
import VerifiedGarbage.Proof.AesOfb.Spec
import VerifiedGarbage.Proof.Modes.RISCV64.Modes
public import VerifiedGarbage.Proof.Modes.Words
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Framework.RISCV64.Steps
import VerifiedGarbage.Proof.Framework.RISCV64.Syms

/-!
# CFB of a message's last piece on RISC-V, for any core

`seqFinal_wp`: `Core.seqFinal c M`, for a core `c` with `CoreSpec c` and a
mode `M` whose operations before the core only copy the chaining value to
the core's buffer (`FinalOk`) and which computes the step function `F`, on
`seq`'s arguments with `len` bytes of data (the precondition is `seq`'s for
data a byte at a time, `byteMode`). With `n = len / L` whole blocks and
`r = len % L` bytes after them: the whole blocks become `F`'s outputs from
the IV, the `r` bytes are XORed with the first bytes of `CIPH_K` of the
chaining value `F` leaves, and the IV becomes that chaining value if
`r = 0`, its image under the cipher otherwise (`finalOut`, `finalNext`).
`cfbEncFinal_wp` and `cfbDecFinal_wp` state this as the specification's
(`Spec.Cfb.encryptFinal`, `decryptFinal`) for `cfbEnc` and `cfbDec`, and
`ofbFinal_wp` as `Spec.Ofb.CryptFinal` for `ofb` (`ofbFinal_out`).

The function is `seq`'s around other loops (`seqWith_changesO_wp`), which
start from `seq`'s invariant for no step (`Inv`, a byte at a time), which
is the invariant for no whole block (`invL`). A whole segment is `seq`'s
step (`pre_wp`, `crypt_step`, `post_wp`) for blocks of `L` bytes, counted
`L` at a time; a partial one runs the same `pre` and core as a step of its
`r` bytes (`fixedT`, `invT`), then copies the buffer to the chaining value
and XORs its first bytes into the data (`xorLoop_wp`).
-/

@[expose] public section

namespace VG.Proof.Modes.RISCV64

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.Modes VG.Impl.Modes.RISCV64
open VG.Spec.Aes (bytesAt)

variable {c : Core}

/-- The mode of the final function's precondition: the data a byte at a
time (`step = 1`), so that `seq`'s precondition gives it `len` bytes, and
the IV written. -/
def byteMode : Mode := { pre := [], post := [], step := 1, ivOut := true }

/-- A mode the final function runs: before the core, the chaining value
copied to the buffer (so the data is read only after it), blocks a step,
and the operations after it a word at a time within the areas. -/
structure FinalOk (c : Core) (M : Mode) : Prop where
  pre : M.pre = copyBlk c.bw .buf .chn
  step : M.step = 4 * c.bw
  post : ∀ o ∈ M.post, o.InBounds (lens c M.step (4 * c.bw))
  postA : ∀ o ∈ M.post, WordAl o

section
variable (c : Core) (s₀ : State)

/-- The whole blocks. -/
abbrev nF : Nat := N s₀ / (4 * c.bw)

/-- The bytes after them. -/
abbrev rF : Nat := N s₀ % (4 * c.bw)

/-- The whole blocks on entry. -/
abbrev xsF : List (List Byte) := chunksAt (4 * c.bw) s₀.mem (Dp s₀) (nF c s₀)

/-- The address of the bytes after them. -/
abbrev tailA : Addr := Dp s₀ + BitVec.ofNat 64 (4 * c.bw * nF c s₀)

end

/-- The data the final function leaves: `F`'s outputs on the whole blocks
from the IV, then the bytes after them XORed with `CIPH_K` of the chaining
value `F` leaves. -/
def finalOut (c : Core) (ciph : Spec.Cbc.Cipher) (F : StepFn) (s₀ : State) : List Byte :=
  (run F (iv0 c s₀) (xsF c s₀)).1.flatten ++
    Spec.Cbc.xor (bytesAt s₀.mem (tailA c s₀) (rF c s₀)) (ciph (run F (iv0 c s₀) (xsF c s₀)).2)

/-- The IV the final function leaves: the chaining value `F` leaves if no
bytes are after the whole blocks, else its image under `CIPH_K`. -/
def finalNext (c : Core) (ciph : Spec.Cbc.Cipher) (F : StepFn) (s₀ : State) : List Byte :=
  if rF c s₀ = 0 then (run F (iv0 c s₀) (xsF c s₀)).2 else ciph (run F (iv0 c s₀) (xsF c s₀)).2

/-! ## Bytes -/

theorem byte_of_chunks1 {m m' : Mem} {D : Addr} {n : Nat} (h : chunksAt 1 m D n = chunksAt 1 m' D n) {i : Nat}
    (hi : i < n) : m (D + BitVec.ofNat 64 i) = m' (D + BitVec.ofNat 64 i) := by
  have e := congrArg (fun l => l[i]?) h
  simpa [chunksAt, bytesAt, hi] using e

theorem bytesAt_congr_of {m m' : Mem} {D : Addr} {n : Nat}
    (h : ∀ i < n, m (D + BitVec.ofNat 64 i) = m' (D + BitVec.ofNat 64 i)) {a l : Nat} (hl : a + l ≤ n) :
    bytesAt m (D + BitVec.ofNat 64 a) l = bytesAt m' (D + BitVec.ofNat 64 a) l :=
  List.map_congr_left fun i hi => by
    have := List.mem_range.mp hi
    rw [VG.Offset.add_add]
    exact h _ (by omega)

theorem chunksAt_congr_of {m m' : Mem} {D : Addr} {n : Nat}
    (h : ∀ i < n, m (D + BitVec.ofNat 64 i) = m' (D + BitVec.ofNat 64 i)) {L k : Nat} (hk : L * k ≤ n) :
    chunksAt L m D k = chunksAt L m' D k :=
  List.map_congr_left fun j hj => by
    have := VG.Proof.Modes.idx_lt (L := L) (List.mem_range.mp hj)
    exact bytesAt_congr_of h (by omega)

theorem chunksAt_one' (m : Mem) (p : Addr) (n : Nat) : chunksAt 1 m p n = bytesSteps (bytesAt m p n) := by
  simp [chunksAt, bytesSteps, bytesAt]

theorem nF_le (c : Core) (s₀ : State) : 4 * c.bw * nF c s₀ ≤ N s₀ := Nat.mul_div_le _ _

theorem nF_rF (c : Core) (s₀ : State) : 4 * c.bw * nF c s₀ + rF c s₀ = N s₀ := Nat.div_add_mod _ _

/-! ## The invariant for no whole block -/

section
variable {cs : CoreSpec c} {F : StepFn} {s₀ s₂ : State} {k : cs.Key}

/-- `seq`'s fixed facts for the data a byte at a time give them for blocks
of `L` bytes, counted `L` at a time. -/
theorem fixedL (hL : 0 < 4 * c.bw)
    (h : Fixed c s₂ (Fb s₀ c) (Dp s₀) (N s₀) 1 (4 * c.bw) (wrs0 c byteMode s₀) (N s₀) 1) :
    Fixed c s₂ (Fb s₀ c) (Dp s₀) (nF c s₀) (4 * c.bw) (4 * c.bw) (wrs0 c byteMode s₀) (N s₀) (4 * c.bw) := by
  have hn := nF_le c s₀
  have hbw : c.bw ≤ 4 := bw_le h.layout
  have hD : (Dp s₀).toNat + 1 * N s₀ ≤ 2 ^ 64 := h.dataFit
  refine ⟨h.scr, fun o w h0 hw => h.dataW o w h0 (show o + w ≤ 1 * N s₀ by omega_arith), by omega_arith,
    (show Region.Disjoint ⟨Dp s₀, 1 * N s₀⟩ _ from h.dataScr).sub_left (Region.sub_prefix (by omega_arith)), h.nFit, hn, by omega_arith,
    ⟨hL, by omega_arith⟩, h.buf, ⟨⟨Dp s₀, 1 * N s₀⟩, List.mem_cons_self, Region.sub_prefix (by omega_arith)⟩, h.scrIn,
    h.layout⟩

/-- `seq`'s invariant for no step, the data a byte at a time, is the
invariant for no whole block. -/
theorem invL (h : Inv cs s₂ (Fb s₀ c) (Dp s₀) (N s₀) 1 (wrs0 c byteMode s₀) (N s₀) 1 k F (iv0 c s₀)
      (xs0 byteMode s₀) 0 s₂) :
    Inv cs s₂ (Fb s₀ c) (Dp s₀) (nF c s₀) (4 * c.bw) (wrs0 c byteMode s₀) (N s₀) (4 * c.bw) k F (iv0 c s₀)
      (xsF c s₀) 0 s₂ := by
  have hd := h.data
  simp only [List.take_zero, run, List.nil_append, List.drop_zero] at hd
  have hb : ∀ i < N s₀, s₂.mem (Dp s₀ + BitVec.ofNat 64 i) = s₀.mem (Dp s₀ + BitVec.ofNat 64 i) :=
    fun i hi => byte_of_chunks1 hd hi
  refine ⟨h.b, fun _ _ _ _ => rfl, rfl, rfl, by rw [h.dp, Nat.mul_zero, Nat.mul_zero],
    by rw [h.np, Nat.mul_zero, Nat.mul_zero], h.ready, ?_, h.chn, Frame.refl _ _⟩
  simp only [List.take_zero, run, List.nil_append, List.drop_zero]
  exact chunksAt_congr_of hb (nF_le c s₀)

end

/-! ## The partial segment's bytes -/

/-- What the byte loop works on: the `r` bytes at `R` (in `s2`, their count
in `s3`) and those at `K` (in `t2`), apart, readable and writable. -/
structure XPre (s₀ : State) (K R : Addr) (r : Nat) : Prop where
  pos : 0 < r
  fK : K.toNat + r ≤ 2 ^ 64
  fR : R.toNat + r ≤ 2 ^ 64
  disj : Region.Disjoint ⟨K, r⟩ ⟨R, r⟩
  rdK : ∀ i < r, InRegions (s₀.rd ++ s₀.wr) (K + BitVec.ofNat 64 i) 1
  wrR : ∀ i < r, InRegions s₀.wr (R + BitVec.ofNat 64 i) 1

/-- The bytes at `R` XORed with those at `K`. -/
abbrev xf (m : Mem) (K R : Addr) : Nat → Byte := fun i => m (R + BitVec.ofNat 64 i) ^^^ m (K + BitVec.ofNat 64 i)

/-- The byte loop, before byte `j`. -/
structure XInv (s₀ : State) (K R : Addr) (r : Nat) (j : Nat) (s : State) : Prop where
  t2 : s.gpr .t2 = K + BitVec.ofNat 64 j
  s2 : s.gpr .s2 = R + BitVec.ofNat 64 j
  s3 : s.gpr .s3 = BitVec.ofNat 64 (r - j)
  lt : j < r
  mem : s.mem = Proof.Modes.over s₀.mem R j (xf s₀.mem K R)
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  gpr : ∀ x, x ≠ .t0 → x ≠ .t1 → x ≠ .t2 → x ≠ .s2 → x ≠ .s3 → s.gpr x = s₀.gpr x

/-- The byte loop, done. -/
structure XDone (s₀ : State) (K R : Addr) (r : Nat) (s : State) : Prop where
  s3 : s.gpr .s3 = BitVec.ofNat 64 0
  mem : s.mem = Proof.Modes.over s₀.mem R r (xf s₀.mem K R)
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  gpr : ∀ x, x ≠ .t0 → x ≠ .t1 → x ≠ .t2 → x ≠ .s2 → x ≠ .s3 → s.gpr x = s₀.gpr x

/-- A byte stored at `P + j` extends `over` of the `j` bytes before it. -/
theorem writeW_over_step {m : Mem} {P : Addr} {j : Nat} {f : Nat → Byte} (hj : j + 1 ≤ 2 ^ 64) :
    (Proof.Modes.over m P j f).writeW (P + BitVec.ofNat 64 j) (f j) = Proof.Modes.over m P (j + 1) f := by
  funext x
  simp only [Mem.writeW, Mem.write, BitVec.setWidth_eq]
  by_cases hx : (x - (P + BitVec.ofNat 64 j)).toNat < 8 / 8
  · rw [ite_eq_left (show (x - (P + BitVec.ofNat 64 j)).toNat < 8 / 8 from hx)]
    have e : (x - P).toNat = j := by bv_omega
    have z : (x - (P + BitVec.ofNat 64 j)).toNat = 0 := by omega_arith
    simp only [Proof.Modes.over]; rw [ite_eq_left (show (x - P).toNat < j + 1 by omega_arith), e, z]
    simp
  · rw [ite_eq_right (show ¬ (x - (P + BitVec.ofNat 64 j)).toNat < 8 / 8 from hx)]
    simp only [Proof.Modes.over]
    by_cases h1 : (x - P).toNat < j
    · rw [ite_eq_left h1, ite_eq_left (show (x - P).toNat < j + 1 by omega_arith)]
    · rw [ite_eq_right h1, ite_eq_right (show ¬ (x - P).toNat < j + 1 by bv_omega)]

theorem inRd_of {s : State} {a : Addr} {n : Nat} (h : InRegions s.wr a n) : InRegions (s.rd ++ s.wr) a n :=
  let ⟨r, hr, hc⟩ := h; ⟨r, List.mem_append_right _ hr, hc⟩

theorem xorStep_wp {s₀ : State} {K R : Addr} {r : Nat} (hp : XPre s₀ K R r) {j : Nat} {s : State}
    (hi : XInv s₀ K R r j s) :
    WP isa (.block xorStep) s fun s' =>
      (isa.eval (.nonzero .s3) s' = some false ∧ XDone s₀ K R r s') ∨
      (isa.eval (.nonzero .s3) s' = some true ∧ XInv s₀ K R r (j + 1) s') := by
  have hj := hi.lt
  have fK := hp.fK
  have fR := hp.fR
  have hr64 : r ≤ 2 ^ 64 := by omega_arith
  have mR : s.mem (R + BitVec.ofNat 64 j) = s₀.mem (R + BitVec.ofNat 64 j) := by
    rw [hi.mem]; exact Proof.Modes.over_out (by rw [Proof.Modes.off_self _ (by omega_arith)]; omega_arith)
  have mK : s.mem (K + BitVec.ofNat 64 j) = s₀.mem (K + BitVec.ofNat 64 j) := by
    rw [hi.mem]
    exact Proof.Modes.over_sep (hp.disj.symm.sub_left (Region.sub_prefix (by omega_arith))) hj hr64
  simp only [xorStep]
  refine wp_lbu (a := R + BitVec.ofNat 64 j) (by decide) (by rw [hi.s2, BitVec.add_zero])
    (by rw [hi.rd, hi.wr]; exact inRd_of (hp.wrR j hj)) fun s₁ u₁ => ?_
  refine wp_lbu (a := K + BitVec.ofNat 64 j) (by decide) (by rw [u₁.other _ (by decide), hi.t2, BitVec.add_zero])
    (by rw [u₁.rd, u₁.wr, hi.rd, hi.wr]; exact hp.rdK j hj) fun s₂ u₂ => ?_
  refine wp_xor fun s₃ u₃ => ?_
  refine wp_sb (a := R + BitVec.ofNat 64 j) (by decide)
    (by rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), hi.s2, BitVec.add_zero])
    (by rw [u₃.wr, u₂.wr, u₁.wr, hi.wr]; exact hp.wrR j hj) fun s₄ u₄ => ?_
  refine wp_addi (imm := 1) (by decide) fun s₅ u₅ => wp_addi (imm := 1) (by decide) fun s₆ u₆ =>
    wp_subi (imm := 1) (by decide) fun s₇ u₇ => WP.block_nil ?_
  have s3₇ : s₇.gpr .s3 = BitVec.ofNat 64 (r - (j + 1)) := by
    rw [u₇.gpr, u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr, u₃.other _ (by decide),
      u₂.other _ (by decide), u₁.other _ (by decide), hi.s3, ofNat_sub64 (by omega_arith), Nat.sub_sub]
  have ev : isa.eval (.nonzero .s3) s₇ = some (decide (r - (j + 1) ≠ 0)) :=
    eval_nonzero_ofNat _ _ (by omega_arith) s3₇
  have mem₇ : s₇.mem = Proof.Modes.over s₀.mem R (j + 1) (xf s₀.mem K R) := by
    rw [u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₃.gpr, u₂.other _ (by decide), u₂.gpr, u₁.gpr, u₁.mem,
      mR, mK, setWidth_xor8, hi.mem]
    exact writeW_over_step (by omega_arith)
  have rd₇ : s₇.rd = s₀.rd := by rw [u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd, hi.rd]
  have wr₇ : s₇.wr = s₀.wr := by rw [u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr, hi.wr]
  have g₇ : ∀ x, x ≠ .t0 → x ≠ .t1 → x ≠ .t2 → x ≠ .s2 → x ≠ .s3 → s₇.gpr x = s₀.gpr x :=
    fun x a b d e f => by
      rw [u₇.other _ f, u₆.other _ d, u₅.other _ e, u₄.gpr, u₃.other _ a, u₂.other _ b, u₁.other _ a,
        hi.gpr x a b d e f]
  by_cases hdone : j + 1 = r
  · exact .inl ⟨ev.trans (by rw [decide_eq_false (by omega_arith)]), ⟨by rw [s3₇, hdone, Nat.sub_self], by rw [mem₇, hdone], rd₇, wr₇, g₇⟩⟩
  · refine .inr ⟨ev.trans (by rw [decide_eq_true (by omega_arith)]), ⟨?_, ?_, s3₇, by omega_arith, mem₇, rd₇, wr₇, g₇⟩⟩
    · rw [u₇.other _ (by decide), u₆.gpr, u₅.other _ (by decide), u₄.gpr, u₃.other _ (by decide),
        u₂.other _ (by decide), u₁.other _ (by decide), hi.t2, VG.Offset.add_add]
    · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.gpr, u₄.gpr, u₃.other _ (by decide),
        u₂.other _ (by decide), u₁.other _ (by decide), hi.s2, VG.Offset.add_add]

/-- The byte loop, from its first byte. -/
theorem xorLoop_wp {s₀ : State} {K R : Addr} {r : Nat} (hp : XPre s₀ K R r) (h0 : XInv s₀ K R r 0 s₀) :
    WP isa (.loop (.block xorStep) (.nonzero .s3)) s₀ (XDone s₀ K R r) := by
  refine WP.loop (M := isa) (fun m s => ∃ j, m = r - j ∧ XInv s₀ K R r j s) (fun m s hs => ?_) r s₀
    ⟨0, by simp, h0⟩
  obtain ⟨j, rfl, hj⟩ := hs
  refine WP.mono (xorStep_wp hp hj) fun s' h => ?_
  rcases h with ⟨z, d⟩ | ⟨z, d⟩
  · exact .inl ⟨z, d⟩
  · exact .inr ⟨z, r - (j + 1), by have := d.lt; have := hj.lt; omega, j + 1, rfl, d⟩

/-- The bytes `over` leaves: those at `R` XORed with those at `K`. -/
theorem bytesAt_over_xf (m : Mem) (K R : Addr) {r L : Nat} (hr : r ≤ L) (h64 : r ≤ 2 ^ 64) :
    bytesAt (Proof.Modes.over m R r (xf m K R)) R r = Spec.Cbc.xor (bytesAt m R r) (bytesAt m K L) := by
  have e : bytesAt (Proof.Modes.over m R r (xf m K R)) R r = (List.range r).map (xf m K R) :=
    List.map_congr_left fun i hi => Proof.Modes.over_at (List.mem_range.mp hi) h64
  rw [e]
  apply List.ext_getElem (by simp [Spec.Cbc.xor, bytesAt]; omega_arith)
  intro i h₁ h₂
  simp only [List.length_map, List.length_range] at h₁
  simp only [List.getElem_map, List.getElem_range, Spec.Cbc.xor, List.getElem_zipWith, bytesAt]

/-! ## Helpers for a segment -/

theorem toNat_add_lt (D : Addr) {a : Nat} (h : D.toNat + a < 2 ^ 64) : (D + BitVec.ofNat 64 a).toNat = D.toNat + a := by
  rw [VG.Offset.toNat_add_ofNat, Nat.mod_eq_of_lt (show a < 2 ^ 64 by omega_arith), Nat.mod_eq_of_lt h]

theorem ofNat_ltu {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    decide (BitVec.ofNat 64 a < BitVec.ofNat 64 b) = decide (a < b) := by
  simp only [BitVec.lt_def, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb]

theorem eval_ltu (s : State) (a b : Reg) : isa.eval (.ltu a b) s = some (decide (s.gpr a < s.gpr b)) := rfl

/-- The operations before the core, the chaining value copied to the
buffer, are the same code whether the data is accessed a word at a time or
not. -/
theorem opsCode_copy_buf (c : Core) (w : Bool) :
    c.opsCode w (copyBlk c.bw .buf .chn) = c.opsCode false (copyBlk c.bw .buf .chn) := by
  simp only [Core.opsCode, copyBlk, List.flatMap_map, Core.opCode, Core.loadW, Core.storeW, Core.wordAt]

theorem copyBlk_ok' {bw : Nat} {dst src : Loc} {ws : List Loc} (hd : dst ∈ ws) {len : Loc → Nat}
    (h1 : 4 * bw ≤ len dst) (h2 : 4 * bw ≤ len src) : ∀ o ∈ copyBlk bw dst src, o.InBounds len ∧ o.dst ∈ ws := by
  intro o ho
  simp only [copyBlk, List.mem_map, List.mem_range] at ho
  obtain ⟨w, hw, rfl⟩ := ho
  refine ⟨⟨?_, ?_, fun _ _ h => by cases h⟩, hd⟩ <;>
    simp only [Op.width, Bool.false_eq_true, ite_false, ite_true] <;> omega_using [hw, h1, h2]

theorem AreasOk.only {s : State} {len : Loc → Nat} {A : Loc → Addr} (h : AreasOk c s len A allLocs)
    (ws : List Loc) : AreasOk c s len A ws :=
  ⟨h.ea, h.disp, h.rd, fun l _ => h.wr l (mem_allLocs l), h.apart, h.fit⟩

/-- `Mid` survives a write of `t0` (that the key stays ready needs the
symbols kept). -/
theorem Mid.tmp {cs : CoreSpec c} {s₀ : State} {B D : Addr} {st bl : Nat} {W : List Region} {j : Nat}
    {k : cs.Key} {s : State} {a : Areas} {s' s'' : State} {v : BitVec 64}
    (hm : Mid cs s₀ B D st bl W j k s a s') (u : Upd s' s'' .t0 v) (sy : s''.syms = s'.syms) :
    Mid cs s₀ B D st bl W j k s a s'' :=
  ⟨by rw [u.other _ (by decide)]; exact hm.b, fun r hr => by rw [u.other r (kept_ne r hr).1]; exact hm.kept r hr,
    by rw [u.rd]; exact hm.rd, by rw [u.wr]; exact hm.wr,
    cs.ready_frame (rs := []) hm.ready (fun r hr _ _ _ _ => u.other r (kept_ne r hr).1) u.rd u.wr sy
      (by rw [u.mem]; exact Frame.refl _ _) (fun _ h => nomatch h) (fun _ h => nomatch h),
    by rw [u.mem]; exact hm.agree, by rw [u.mem]; exact hm.frame⟩

/-- The buffer after the core, when the operations before it copied the
chaining value there. -/
theorem rd_cryptBuf_copy {bw : Nat} (ciph : Spec.Cbc.Cipher) (hc : ∀ b, (ciph b).length = 4 * bw) (a : Areas) :
    rd (cryptBuf (4 * bw) ciph (applyOps (copyBlk bw .buf .chn) a)) .buf (4 * bw) = ciph (rd a .chn (4 * bw)) := by
  have e : rd (applyOps (copyBlk bw .buf .chn) a) .buf (4 * bw) = rd a .chn (4 * bw) :=
    List.map_congr_left fun i hi => by
      rw [copyBlk_apply (by decide), ite_eq_left ⟨rfl, List.mem_range.mp hi⟩]
  refine rd_eq (by rw [hc]) fun i hi => ?_
  simp only [cryptBuf, e, ite_true]

/-- The data's area after the core, when the operations before it copied
the chaining value to the buffer. -/
theorem cryptBuf_copy_dat {bw n : Nat} (ciph : Spec.Cbc.Cipher) (a : Areas) (i : Nat) :
    cryptBuf n ciph (applyOps (copyBlk bw .buf .chn) a) .dat i = a .dat i := by
  simp only [cryptBuf, reduceCtorEq, ite_false]
  rw [copyBlk_apply (by decide), ite_eq_right (by simp)]

theorem cryptBuf_copy_chn {bw n : Nat} (ciph : Spec.Cbc.Cipher) (a : Areas) (i : Nat) :
    cryptBuf n ciph (applyOps (copyBlk bw .buf .chn) a) .chn i = a .chn i := by
  simp only [cryptBuf, reduceCtorEq, ite_false]
  rw [copyBlk_apply (by decide), ite_eq_right (by simp)]

/-! ## The segments -/

/-- The invariant after `j` whole blocks. -/
abbrev IL (cs : CoreSpec c) (F : StepFn) (s₀ s₂ : State) (k : cs.Key) (j : Nat) (s : State) : Prop :=
  Inv cs s₂ (Fb s₀ c) (Dp s₀) (nF c s₀) (4 * c.bw) (wrs0 c byteMode s₀) (N s₀) (4 * c.bw) k F (iv0 c s₀)
    (xsF c s₀) j s

/-- The final function's loops' result. -/
abbrev FDone (cs : CoreSpec c) (F : StepFn) (s₀ s₂ : State) (k : cs.Key) (s : State) : Prop :=
  DoneO (c := c) s₂ (Fb s₀ c) (Dp s₀) (N s₀) byteMode.step (bytesSteps (finalOut c (cs.cipher k) F s₀))
    (finalNext c (cs.cipher k) F s₀) s

section
variable {cs : CoreSpec c} {M : Mode} {F : StepFn} {s₀ s₂ : State} {k : cs.Key} {w : Bool}

theorem coreScr {B : Addr} (hL : Layout c) : Region.Sub (coreRegion c B) (scrRegion c B) := by
  have := buf_le4 hL; have := hL.buf_ge
  exact VG.Offset.sub_base _ (by simp only [coreSlot] at *; omega_arith)

theorem chnScr {B : Addr} (hL : Layout c) : Region.Sub (chnRegion c B) (scrRegion c B) := by
  have := buf_le4 hL; have := hL.buf_ge; have := bw_le hL
  exact VG.Offset.sub_base _ (by simp only [Core.chnSlot, coreSlot] at *; omega_arith)

/-- The regions a run of whole blocks changes are among those of the
function. -/
theorem big_sub {B D : Addr} {n L N : Nat} (h : L * n ≤ N) :
    ∀ r ∈ big c B D n L, ∃ r' ∈ big c B D N 1, Region.Sub r r' := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact ⟨_, List.mem_cons_self, fun _ h => h⟩
  · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, fun _ h => h⟩
  · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self),
      Region.sub_prefix (by omega_arith)⟩

/-- No bytes after the whole blocks: done. -/
theorem done_whole {j : Nat} (hj : j = nF c s₀) {t : State} (hI : IL cs F s₀ s₂ k j t) (hr : rF c s₀ = 0) :
    FDone cs F s₀ s₂ k t := by
  subst hj
  have hx : (xsF c s₀).take (nF c s₀) = xsF c s₀ := List.take_of_length_le (by rw [chunksAt_length])
  have hd : (xsF c s₀).drop (nF c s₀) = [] := List.drop_of_length_le (by rw [chunksAt_length])
  have hN : 4 * c.bw * nF c s₀ = N s₀ := by have := nF_rF c s₀; omega
  have data := hI.data
  rw [hx, hd, List.append_nil] at data
  refine ⟨hI.b, hI.keep, hI.rd, hI.wr, ?_, ?_, hI.frame.sub (big_sub (nF_le c s₀))⟩
  · show chunksAt 1 t.mem (Dp s₀) (N s₀) = _
    rw [chunksAt_one']
    refine congrArg bytesSteps ?_
    have e := VG.Proof.Modes.bytesAt_mul (4 * c.bw) t.mem (Dp s₀) (nF c s₀)
    rw [hN] at e
    rw [e, finalOut, hr]
    simp only [bytesAt, List.range_zero, List.map_nil, Spec.Cbc.xor, List.zipWith_nil_left, List.append_nil]
    exact congrArg List.flatten data
  · rw [hI.chn, hx, finalNext, ite_eq_left hr]

/-- A whole block: `seq`'s step. -/
theorem whole_seg (hM : FinalOk c M) (hcomp : Computes M (4 * c.bw) (cs.cipher k) F)
    (hF : Fixed c s₂ (Fb s₀ c) (Dp s₀) (nF c s₀) (4 * c.bw) (4 * c.bw) (wrs0 c byteMode s₀) (N s₀) (4 * c.bw))
    (hw : WordOk c w M (Fb s₀ c) (Dp s₀) (4 * c.bw)) {j : Nat} (hj : 4 * c.bw * (j + 1) ≤ N s₀) {t : State}
    (hI : IL cs F s₀ s₂ k j t) : WP isa (c.seg w M) t (IL cs F s₀ s₂ k (j + 1)) := by
  have hbw := bw_le hF.layout
  have hL : 0 < 4 * c.bw := hF.step.1
  have hjn : j < nF c s₀ := by
    have := (Nat.le_div_iff_mul_le hL).mpr (show (j + 1) * (4 * c.bw) ≤ N s₀ by rw [Nat.mul_comm]; exact hj)
    show j < N s₀ / (4 * c.bw)
    omega
  have hpre : ∀ o ∈ M.pre, o.InBounds (lens c (4 * c.bw) (4 * c.bw)) := by
    rw [hM.pre]
    exact fun o ho => (copyBlk_ok' (ws := allLocs) (mem_allLocs _) (by simp [lens]) (by simp [lens]) o ho).1
  have hpost : ∀ o ∈ M.post, o.InBounds (lens c (4 * c.bw) (4 * c.bw)) := by
    have := hM.post; rw [hM.step] at this; exact this
  unfold Core.seg
  refine WP.seq (WP.mono (pre_wp cs hF hw hpre hjn hI) fun s₁ h₁ => ?_)
  refine WP.seq (WP.mono (crypt_step cs hF (bufCipher_one hF.layout.G_pos _) hjn h₁) fun s₃ h₃ => ?_)
  refine WP.seq (WP.of_syms (wp_li (imm := 4 * c.bw) (by omega_arith) fun s₄ u₄ => WP.block_nil fun sy₄ => ?_))
  have h₄ := h₃.tmp u₄ sy₄
  have s3₄ : s₄.gpr .s3 = BitVec.ofNat 64 (N s₀ - 4 * c.bw * j) := by
    rw [u₄.other _ (by decide), h₃.kept _ (mem_kept (by simp)), hI.np]
  have ev : isa.eval (.ltu .s3 .t0) s₄ = some false := by
    rw [Nat.mul_succ] at hj
    rw [eval_ltu, s3₄, u₄.gpr, ofNat_ltu (by have := hF.nFit; omega_arith) (by omega_arith),
      decide_eq_false (by omega_arith)]
  refine WP.ite false ev (fun h => nomatch h) fun _ => ?_
  have e : c.opsCode w M.post ++ c.advanceBytes =
      c.opsCode w M.post ++ (.addi .s2 .s2 (M.step : Int) :: .addi .s3 .s3 (-((4 * c.bw : Nat) : Int)) :: []) := by
    rw [hM.step]; rfl
  rw [e]
  exact WP.mono (post_wp cs hF hw hM.step hpost hcomp exOk_nil (chunksAt_length _ _ _ _) hjn hI h₄) fun _ h => h.1

/-- A partial segment: the step of its `r` bytes, then the buffer to the
chaining value and its first `r` bytes XORed into them. -/
theorem tail_seg (hM : FinalOk c M)
    (hfx : Fixed c s₂ (Fb s₀ c) (Dp s₀) (N s₀) 1 (4 * c.bw) (wrs0 c byteMode s₀) (N s₀) 1)
    (hb : ∀ i < N s₀, s₂.mem (Dp s₀ + BitVec.ofNat 64 i) = s₀.mem (Dp s₀ + BitVec.ofNat 64 i))
    (hr : 0 < rF c s₀) {j : Nat} (hj : j = nF c s₀) {t : State} (hI : IL cs F s₀ s₂ k j t) :
    WP isa (c.seg w M) t fun t' => isa.eval (.nonzero .s3) t' = some false ∧ FDone cs F s₀ s₂ k t' := by
  subst hj
  have hL := hfx.layout
  have hbw := bw_le hL
  have hb4 := buf_le4 hL
  have hge := hL.buf_ge
  have h6 : coreSlot = 6 := rfl
  have hnr := nF_rF c s₀
  have hbw0 : 0 < c.bw := by rcases hL.bw with h | h <;> omega_using [h]
  have hrL : rF c s₀ < 4 * c.bw := Nat.mod_lt _ (by omega_using [hbw0])
  have hD : (Dp s₀).toNat + 1 * N s₀ ≤ 2 ^ 64 := hfx.dataFit
  have hNf : N s₀ < 2 ^ 64 := hfx.nFit
  have hS := hfx.scr
  have hfit := hS.fit
  have wrt : t.wr = s₂.wr := hI.wr
  have hTA : (tailA c s₀).toNat = (Dp s₀).toNat + 4 * c.bw * nF c s₀ := toNat_add_lt _ (by omega_arith)
  -- The partial segment as a step of its own.
  have hT : Fixed c t (Fb s₀ c) (tailA c s₀) 1 (rF c s₀) (4 * c.bw) (wrs0 c byteMode s₀) (rF c s₀) 1 := by
    refine ⟨hS.congr wrt, fun o w h0 hw => ?_, by rw [hTA]; omega_arith, ?_, by omega_arith, by omega_arith,
      by decide, ⟨hr, by omega_arith⟩, hfx.buf, ⟨⟨Dp s₀, 1 * N s₀⟩, List.mem_cons_self, ?_⟩, hfx.scrIn, hL⟩
    · show InRegions t.wr (Dp s₀ + BitVec.ofNat 64 (4 * c.bw * nF c s₀) + BitVec.ofNat 64 o) w
      rw [wrt, VG.Offset.add_add]; exact hfx.dataW _ _ h0 (by omega_arith)
    · exact (show Region.Disjoint ⟨Dp s₀, 1 * N s₀⟩ _ from hfx.dataScr).sub_left
        (VG.Offset.sub_base _ (by omega_arith))
    · exact VG.Offset.sub_base _ (by omega_arith)
  have hIT : Inv cs t (Fb s₀ c) (tailA c s₀) 1 (rF c s₀) (wrs0 c byteMode s₀) (rF c s₀) 1 k F
      (bytesAt t.mem (slotA (Fb s₀ c) Core.chnSlot) (4 * c.bw)) (chunksAt (rF c s₀) t.mem (tailA c s₀) 1) 0 t := by
    refine ⟨hI.b, fun _ _ _ _ => rfl, rfl, rfl, by rw [hI.dp, Nat.mul_zero, BitVec.add_zero],
      hI.np.trans (congrArg _ (by omega_arith)), hI.ready, ?_, ?_, Frame.refl _ _⟩
    · simp only [List.take_zero, run, List.nil_append, List.drop_zero]
    · simp only [List.take_zero, run]
  have hwT : WordOk c false M (Fb s₀ c) (tailA c s₀) (rF c s₀) :=
    ⟨by rw [hM.pre]; exact copyBlk_wordAl _ _ _, hM.postA, by have := hS.al; omega, fun h => nomatch h⟩
  have hpreT : ∀ o ∈ M.pre, o.InBounds (lens c (rF c s₀) (4 * c.bw)) := by
    rw [hM.pre]
    exact fun o ho => (copyBlk_ok' (ws := allLocs) (mem_allLocs _) (by simp [lens]) (by simp [lens]) o ho).1
  unfold Core.seg
  rw [hM.pre, opsCode_copy_buf, ← hM.pre]
  refine WP.seq (WP.mono (pre_wp cs hT hwT hpreT Nat.zero_lt_one hIT) fun s₁ h₁ => ?_)
  refine WP.seq (WP.mono (crypt_step cs hT (bufCipher_one hL.G_pos _) Nat.zero_lt_one h₁) fun s₃ h₃ => ?_)
  refine WP.seq (WP.of_syms (wp_li (imm := 4 * c.bw) (by omega_arith) fun s₄ u₄ => WP.block_nil fun sy₄ => ?_))
  have h₄ := h₃.tmp u₄ sy₄
  rw [hM.pre] at h₄
  have kp₄ : ∀ r, r = .a0 ∨ r = .s1 ∨ r = .s3 ∨ r = .s2 → s₄.gpr r = t.gpr r := fun r hr => by
    rw [u₄.other _ (by rcases hr with rfl | rfl | rfl | rfl <;> decide)]; exact h₃.kept r (mem_kept hr)
  have ev : isa.eval (.ltu .s3 .t0) s₄ = some true := by
    rw [eval_ltu, kp₄ _ (by simp), hIT.np, u₄.gpr, ofNat_ltu (by omega_arith) (by omega_arith),
      decide_eq_true (by omega_arith)]
  refine WP.ite true ev (fun _ => ?_) (fun h => nomatch h)
  unfold Core.tail
  apply WP.seq
  -- The buffer to the chaining value.
  have hA : AreasOk c s₄ (lens c (rF c s₀) (4 * c.bw)) (areas c (Fb s₀ c) (tailA c s₀) (rF c s₀) 0) [.chn] :=
    (areasOk hT Nat.zero_lt_one h₄.b (by rw [kp₄ _ (by simp)]; exact hIT.dp) h₄.wr).only _
  refine opsCode_wp c false (areas_al hwT 0) (copyBlk_ok' (List.mem_singleton_self _) (by simp [lens])
    (by simp [lens])) (copyBlk_wordAl _ _ _) hA fun s₅ a₅ f₅ g₅ rd₅ wr₅ => ?_
  refine wp_addi (imm := 8 * c.buf) (by omega_arith) fun s₆ u₆ => WP.block_nil ?_
  have g₆ : ∀ r, r ≠ .t0 → r ≠ .t1 → r ≠ .t2 → s₆.gpr r = s₄.gpr r := fun r h0 h1 h2 => by
    rw [u₆.other r h2, g₅ r h0 h1 h2]
  have wr₆ : s₆.wr = s₂.wr := by rw [u₆.wr, wr₅, h₄.wr, wrt]
  have rd₆ : s₆.rd = s₂.rd := by rw [u₆.rd, rd₅, h₄.rd, hI.rd]
  -- The byte loop.
  have hK : (slotA (Fb s₀ c) c.buf).toNat = (Fb s₀ c).toNat + 8 * c.buf := toNat_add_lt _ (by omega_arith)
  have subK : Region.Sub ⟨slotA (Fb s₀ c) c.buf, rF c s₀⟩ (scrRegion c (Fb s₀ c)) :=
    VG.Offset.sub_base _ (by omega_arith)
  have subR : Region.Sub ⟨tailA c s₀, rF c s₀⟩ ⟨Dp s₀, 1 * N s₀⟩ := VG.Offset.sub_base _ (by omega_arith)
  have dRS : Region.Disjoint ⟨tailA c s₀, rF c s₀⟩ (scrRegion c (Fb s₀ c)) :=
    (show Region.Disjoint ⟨Dp s₀, 1 * N s₀⟩ _ from hfx.dataScr).sub_left subR
  have hX : XPre s₆ (slotA (Fb s₀ c) c.buf) (tailA c s₀) (rF c s₀) := by
    refine ⟨hr, by rw [hK]; omega_arith, by rw [hTA]; omega_arith, (dRS.sub_right subK).symm,
      fun i hi => ?_, fun i hi => ?_⟩
    · rw [rd₆, wr₆, VG.Offset.add_add]; exact inRd_of (hS.low _ _ (by omega_arith))
    · show InRegions s₆.wr (Dp s₀ + BitVec.ofNat 64 (4 * c.bw * nF c s₀) + BitVec.ofNat 64 i) 1
      rw [wr₆, VG.Offset.add_add]; exact hfx.dataW _ _ (by decide) (by omega_arith)
  have hX0 : XInv s₆ (slotA (Fb s₀ c) c.buf) (tailA c s₀) (rF c s₀) 0 s₆ := by
    refine ⟨?_, ?_, ?_, hr, by rw [Proof.Modes.over_zero], rfl, rfl, fun _ _ _ _ _ _ => rfl⟩
    · rw [u₆.gpr, g₅ _ (by decide) (by decide) (by decide), h₄.b, BitVec.add_zero]
    · rw [g₆ _ (by decide) (by decide) (by decide), kp₄ _ (by simp), hIT.dp, BitVec.add_zero, Nat.mul_zero,
        BitVec.add_zero]
    · rw [g₆ _ (by decide) (by decide) (by decide), kp₄ _ (by simp), hIT.np]
  refine WP.mono (xorLoop_wp hX hX0) fun s₇ h₇ => ⟨by rw [eval_nonzero_ofNat _ _ (by decide) h₇.s3]; rfl, ?_⟩
  -- The memory, region by region.
  have hx : (xsF c s₀).take (nF c s₀) = xsF c s₀ := List.take_of_length_le (by rw [chunksAt_length])
  have hd : (xsF c s₀).drop (nF c s₀) = [] := List.drop_of_length_le (by rw [chunksAt_length])
  have hc := cs.cipher_len k
  have dat0 : datRegion (tailA c s₀) (rF c s₀) 0 = ⟨tailA c s₀, rF c s₀⟩ := by
    simp only [datRegion, Nat.mul_zero, BitVec.add_zero]
  have hcs := coreScr (B := Fb s₀ c) hL
  have hhs := chnScr (B := Fb s₀ c) hL
  have dRC : Region.Disjoint ⟨tailA c s₀, rF c s₀⟩ (chnRegion c (Fb s₀ c)) := dRS.sub_right hhs
  have dKC : Region.Disjoint ⟨slotA (Fb s₀ c) c.buf, 4 * c.bw⟩ (chnRegion c (Fb s₀ c)) :=
    VG.Offset.disjoint _ (.inr (by simp only [Core.chnSlot]; omega_arith)) (by omega_arith)
      (by simp only [Core.chnSlot]; omega_arith)
  have f₅' : Frame [chnRegion c (Fb s₀ c)] s₄.mem s₆.mem := by
    rw [u₆.mem]; exact f₅
  -- The buffer after the core: `CIPH_K` of the chaining value.
  have buf₄ : bytesAt s₄.mem (slotA (Fb s₀ c) c.buf) (4 * c.bw) = cs.cipher k (run F (iv0 c s₀) (xsF c s₀)).2 := by
    have e := rd_agree h₄.agree (l := .buf) (n := 4 * c.bw) (by simp [lens])
    rw [rd_cryptBuf_copy _ hc] at e
    have e2 : rd (cont (areas c (Fb s₀ c) (tailA c s₀) (rF c s₀) 0) t.mem) .chn (4 * c.bw) =
        (run F (iv0 c s₀) (xsF c s₀)).2 := by rw [← hx]; exact hI.chn
    rw [e2] at e
    exact e
  have buf₆ : bytesAt s₆.mem (slotA (Fb s₀ c) c.buf) (4 * c.bw) = cs.cipher k (run F (iv0 c s₀) (xsF c s₀)).2 := by
    rw [← buf₄]
    exact List.map_congr_left fun i hi => f₅'.bytes (R := ⟨slotA (Fb s₀ c) c.buf, 4 * c.bw⟩)
      (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact dKC) (show 4 * c.bw ≤ 2 ^ 64 by omega_arith)
      (List.mem_range.mp hi)
  -- The chaining value after the copy: the buffer.
  have chn₆ : bytesAt s₆.mem (slotA (Fb s₀ c) Core.chnSlot) (4 * c.bw) =
      cs.cipher k (run F (iv0 c s₀) (xsF c s₀)).2 := by
    rw [← buf₄, u₆.mem]
    refine List.map_congr_left fun i hi => ?_
    have hi := List.mem_range.mp hi
    have e := a₅ .chn i (by simp [lens]; exact hi)
    simp only [cont, areas] at e
    rw [e, copyBlk_apply (by decide), ite_eq_left ⟨rfl, hi⟩]
    rfl
  -- The data's bytes after the core: as before it.
  have dat₄ : ∀ i < rF c s₀, s₄.mem (tailA c s₀ + BitVec.ofNat 64 i) = t.mem (tailA c s₀ + BitVec.ofNat 64 i) :=
    fun i hi => by
      have e := h₄.agree .dat i (by simp [lens]; exact hi)
      rw [cryptBuf_copy_dat] at e
      simpa [cont, areas] using e
  have tl₆ : bytesAt s₆.mem (tailA c s₀) (rF c s₀) = bytesAt s₀.mem (tailA c s₀) (rF c s₀) := by
    refine List.map_congr_left fun i hi => ?_
    have hi := List.mem_range.mp hi
    rw [f₅'.bytes (R := ⟨tailA c s₀, rF c s₀⟩) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact dRC) (show rF c s₀ ≤ 2 ^ 64 by omega_arith) hi,
      dat₄ i hi]
    rw [hI.frame.bytes (R := ⟨tailA c s₀, rF c s₀⟩) (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact dRS.sub_right hcs
        · exact dRC
        · exact (VG.Offset.base_disjoint _ (Nat.le_refl _) (by omega_arith)).symm)
      (show rF c s₀ ≤ 2 ^ 64 by omega_arith) hi]
    show s₂.mem (Dp s₀ + BitVec.ofNat 64 (4 * c.bw * nF c s₀) + BitVec.ofNat 64 i) =
      s₀.mem (Dp s₀ + BitVec.ofNat 64 (4 * c.bw * nF c s₀) + BitVec.ofNat 64 i)
    rw [VG.Offset.add_add]; exact hb _ (by omega_arith)
  -- What the segment changed.
  have fT : Frame [⟨tailA c s₀, rF c s₀⟩, coreRegion c (Fb s₀ c), chnRegion c (Fb s₀ c)] t.mem s₇.mem := by
    have f₄ : Frame [⟨tailA c s₀, rF c s₀⟩, coreRegion c (Fb s₀ c), chnRegion c (Fb s₀ c)] t.mem s₄.mem := by
      rw [← dat0]; exact h₄.frame
    refine (f₄.trans (f₅'.mono (by simp))).trans ?_
    rw [h₇.mem]
    exact (Proof.Modes.over_frame _ _ _ _).mono (by simp)
  have dBlk : ∀ r ∈ [(⟨tailA c s₀, rF c s₀⟩ : Region), coreRegion c (Fb s₀ c), chnRegion c (Fb s₀ c)],
      Region.Disjoint (dataRegion (Dp s₀) (4 * c.bw) (nF c s₀)) r := by
    have dS : Region.Disjoint (dataRegion (Dp s₀) (4 * c.bw) (nF c s₀)) (scrRegion c (Fb s₀ c)) :=
      (show Region.Disjoint ⟨Dp s₀, 1 * N s₀⟩ _ from hfx.dataScr).sub_left (Region.sub_prefix (by omega_arith))
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact VG.Offset.base_disjoint _ (Nat.le_refl _) (by omega_arith)
    · exact dS.sub_right hcs
    · exact dS.sub_right hhs
  refine ⟨?_, fun r hr h3 h2 => ?_, by rw [h₇.rd, rd₆], by rw [h₇.wr, wr₆], ?_, ?_, ?_⟩
  · rw [h₇.gpr _ (by decide) (by decide) (by decide) (by decide) (by decide), g₆ _ (by decide) (by decide)
      (by decide)]
    exact h₄.b
  · have hk := kept_ne r hr
    rw [h₇.gpr r hk.1 hk.2.1 hk.2.2 h2 h3, g₆ r hk.1 hk.2.1 hk.2.2, u₄.other r hk.1, h₃.kept r hr,
      hI.keep r hr h3 h2]
  · show chunksAt 1 s₇.mem (Dp s₀) (N s₀) = _
    rw [chunksAt_one']
    refine congrArg bytesSteps ?_
    rw [VG.Proof.Modes.bytesAt_blocks_tail (4 * c.bw) s₇.mem (Dp s₀) (N s₀)]
    have blk : chunksAt (4 * c.bw) s₇.mem (Dp s₀) (nF c s₀) = (run F (iv0 c s₀) (xsF c s₀)).1 := by
      rw [chunksAt_frame fT dBlk (by omega_arith)]
      have data := hI.data
      rw [hx, hd, List.append_nil] at data
      exact data
    have tl : bytesAt s₇.mem (tailA c s₀) (rF c s₀) =
        Spec.Cbc.xor (bytesAt s₀.mem (tailA c s₀) (rF c s₀)) (cs.cipher k (run F (iv0 c s₀) (xsF c s₀)).2) := by
      rw [h₇.mem, bytesAt_over_xf _ _ _ (Nat.le_of_lt hrL) (by omega_arith), tl₆, buf₆]
    rw [finalOut]
    exact congr (congrArg (· ++ ·) (congrArg List.flatten blk)) tl
  · rw [finalNext, ite_eq_right (by omega_arith), ← chn₆, h₇.mem]
    exact List.map_congr_left fun i hi =>
      Proof.Modes.over_sep dRC (List.mem_range.mp hi) (by omega_arith)
  · exact (hI.frame.sub (big_sub (nF_le c s₀))).trans (fT.sub fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self), subR⟩
      · exact ⟨_, List.mem_cons_self, fun _ h => h⟩
      · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, fun _ h => h⟩)

/-- The segments, from `seq`'s invariant for no step. -/
theorem segs_ok (hM : FinalOk c M) (hcomp : Computes M (4 * c.bw) (cs.cipher k) F)
    (hD : w = true → (Dp s₀).toNat % 4 = 0 ∧ M.step % 4 = 0) :
    LoopsOkO cs byteMode F s₀ k (bytesSteps (finalOut c (cs.cipher k) F s₀)) (finalNext c (cs.cipher k) F s₀)
      (c.segs w M) := by
  intro s₂ hfx hI0
  have hL := hfx.layout
  have hbw0 : 0 < c.bw := by rcases hL.bw with h | h <;> omega_using [h]
  have hL0 : 0 < 4 * c.bw := by omega_arith
  have hFL := fixedL hL0 hfx
  have hIL := invL hI0
  have hNf : N s₀ < 2 ^ 64 := hfx.nFit
  have hd0 := hI0.data
  simp only [List.take_zero, run, List.nil_append, List.drop_zero] at hd0
  have hb : ∀ i < N s₀, s₂.mem (Dp s₀ + BitVec.ofNat 64 i) = s₀.mem (Dp s₀ + BitVec.ofNat 64 i) :=
    fun i hi => byte_of_chunks1 hd0 hi
  have hw : WordOk c w M (Fb s₀ c) (Dp s₀) (4 * c.bw) :=
    ⟨by rw [hM.pre]; exact copyBlk_wordAl _ _ _, hM.postA, by have := hfx.scr.al; omega,
      fun h => by have := hD h; rw [hM.step] at this; exact this⟩
  have hnr := nF_rF c s₀
  unfold Core.segs
  by_cases hN0 : N s₀ = 0
  · refine WP.ite true (by rw [eval_zero_ofNat _ _ (by omega_arith) hIL.np]; simp [hN0]) (fun _ => ?_)
      (fun h => nomatch h)
    exact WP.block_nil (done_whole (j := 0) (by show 0 = N s₀ / (4 * c.bw); rw [hN0, Nat.zero_div]) hIL
      (by show N s₀ % (4 * c.bw) = 0; rw [hN0, Nat.zero_mod]))
  refine WP.ite false (by rw [eval_zero_ofNat _ _ (by omega_arith) hIL.np]; simp [hN0]) (fun h => nomatch h)
    fun _ => ?_
  refine WP.loop (M := isa) (fun m t => ∃ j, m = N s₀ - 4 * c.bw * j ∧ 4 * c.bw * j < N s₀ ∧ IL cs F s₀ s₂ k j t)
    (fun m t ⟨j, hm, hj, h⟩ => ?_) _ s₂ ⟨0, rfl, by omega_arith, hIL⟩
  subst hm
  by_cases hwh : 4 * c.bw * (j + 1) ≤ N s₀
  · refine WP.mono (whole_seg hM hcomp hFL hw hwh h) fun t' h' => ?_
    have ev := eval_nonzero_ofNat t' .s3 (by omega_arith) h'.np
    by_cases hend : 4 * c.bw * (j + 1) = N s₀
    · have hn : j + 1 = nF c s₀ := by
        show j + 1 = N s₀ / (4 * c.bw)
        rw [← hend, Nat.mul_div_cancel_left _ hL0]
      exact .inl ⟨ev.trans (by rw [decide_eq_false (by omega_arith)]), done_whole hn h'
        (by show N s₀ % (4 * c.bw) = 0; rw [← hend, Nat.mul_mod_right])⟩
    · exact .inr ⟨ev.trans (by rw [decide_eq_true (by omega_arith)]), _,
        by rw [Nat.mul_succ] at hwh ⊢; omega_arith, j + 1, rfl, by omega_arith, h'⟩
  · have hjn : j = nF c s₀ := by
      show j = N s₀ / (4 * c.bw)
      have h1 := (Nat.div_lt_iff_lt_mul hL0).mpr (show N s₀ < (j + 1) * (4 * c.bw) by
        rw [Nat.mul_comm]; omega_arith)
      have h2 := (Nat.le_div_iff_mul_le hL0).mpr (show j * (4 * c.bw) ≤ N s₀ by rw [Nat.mul_comm]; omega_arith)
      omega_arith
    have hr : 0 < rF c s₀ := by
      show 0 < N s₀ % (4 * c.bw)
      have := Nat.div_add_mod (N s₀) (4 * c.bw)
      rw [← show j = N s₀ / (4 * c.bw) from hjn] at this
      omega_arith
    exact WP.mono (tail_seg hM hfx hb hr hjn h) fun t' h' => .inl h'

end

/-! ## The function -/

/-- `Core.seqFinal c M` on `seq`'s arguments with `len` bytes of data: the
data becomes `finalOut`, the IV `finalNext`; and what it changes
(`Changes`). -/
theorem seqFinal_wp (cs : CoreSpec c) {M : Mode} {F : StepFn} {s₀ : State} {k : cs.Key}
    (hM : FinalOk c M) (hcomp : Computes M (4 * c.bw) (cs.cipher k) F)
    (hp : SeqPre c byteMode s₀) (hk : cs.KeyArgs s₀ (wrs0 c byteMode s₀) k) :
    WP isa (c.seqFinal M) s₀ fun s' => abiPreserved s₀ s' ∧
      bytesAt s'.mem (Dp s₀) (N s₀) = finalOut c (cs.cipher k) F s₀ ∧
      bytesAt s'.mem (P s₀) (4 * c.bw) = finalNext c (cs.cipher k) F s₀ ∧ Changes c byteMode s₀ s' :=
  WP.mono (seqWith_changesO_wp cs (F := F) hp (aligned_okO cs (st := M.step) fun _ hw => segs_ok hM hcomp hw) hk)
    fun s' ⟨h1, h2, h3, h4⟩ => ⟨h1, by
      have e : chunksAt 1 s'.mem (Dp s₀) (N s₀) = _ := h2
      rw [chunksAt_one'] at e
      rw [← bytesSteps_flatten (bytesAt s'.mem (Dp s₀) (N s₀)), e, bytesSteps_flatten], h3 rfl, h4⟩

/-! ## CFB -/

theorem cfbEnc_finalOk (c : Core) : FinalOk c (Mode.cfbEnc c.bw) :=
  ⟨rfl, rfl, fun o ho => by
    have b := blk_bounds (c := c) (st := (Mode.cfbEnc c.bw).step) rfl
    exact append_ok (xorBlk_inBounds (b _) (b _) (b _)) (copyBlk_inBounds (b _) (b _)) o ho,
    append_ok (xorBlk_wordAl _ _ _ _) (copyBlk_wordAl _ _ _)⟩

theorem cfbDec_finalOk (c : Core) : FinalOk c (Mode.cfbDec c.bw) :=
  ⟨rfl, rfl, fun o ho => by
    have b := blk_bounds (c := c) (st := (Mode.cfbDec c.bw).step) rfl
    exact append_ok (copyBlk_inBounds (b _) (b _)) (xorBlk_inBounds (b _) (b _) (b _)) o ho,
    append_ok (copyBlk_wordAl _ _ _) (xorBlk_wordAl _ _ _ _)⟩

/-- CFB encryption of a message's last piece, as the specification's. -/
theorem cfbEncFinal_wp (cs : CoreSpec c) {s₀ : State} {k : cs.Key} (hp : SeqPre c byteMode s₀)
    (hk : cs.KeyArgs s₀ (wrs0 c byteMode s₀) k) :
    WP isa (c.seqFinal (Mode.cfbEnc c.bw)) s₀ fun s' => abiPreserved s₀ s' ∧
      Spec.Cfb.EncryptFinal (cs.cipher k) (4 * c.bw) s₀.mem s'.mem (P s₀) (Dp s₀) (N s₀) ∧
      Changes c byteMode s₀ s' :=
  WP.mono (seqFinal_wp cs (cfbEnc_finalOk c) (cfbEnc_computes (cs.cipher_len k)) hp hk)
    fun s' ⟨h1, h2, h3, h4⟩ => ⟨h1, ⟨by
      rw [h2, finalOut, Spec.Cfb.encryptFinal, Proof.Modes.segments_bytesAt, Proof.Modes.tail_bytesAt,
        ← (cfbEnc_run _ _ _).1, ← (cfbEnc_run _ _ _).2]; rfl, by
      rw [h3, ← Proof.Modes.cfbEncFinalNext_of, finalNext, ← (cfbEnc_run _ _ _).2]; rfl⟩,
      h4⟩

/-- CFB decryption of a message's last piece, as the specification's. -/
theorem cfbDecFinal_wp (cs : CoreSpec c) {s₀ : State} {k : cs.Key} (hp : SeqPre c byteMode s₀)
    (hk : cs.KeyArgs s₀ (wrs0 c byteMode s₀) k) :
    WP isa (c.seqFinal (Mode.cfbDec c.bw)) s₀ fun s' => abiPreserved s₀ s' ∧
      Spec.Cfb.DecryptFinal (cs.cipher k) (4 * c.bw) s₀.mem s'.mem (P s₀) (Dp s₀) (N s₀) ∧
      Changes c byteMode s₀ s' :=
  WP.mono (seqFinal_wp cs (cfbDec_finalOk c) (cfbDec_computes (cs.cipher_len k)) hp hk)
    fun s' ⟨h1, h2, h3, h4⟩ => ⟨h1, ⟨by
      rw [h2, finalOut, Spec.Cfb.decryptFinal, Proof.Modes.segments_bytesAt, Proof.Modes.tail_bytesAt,
        ← (cfbDec_run _ _ _).1, ← (cfbDec_run _ _ _).2]; rfl, by
      rw [h3, ← Proof.Modes.cfbDecFinalNext_of, finalNext, ← (cfbDec_run _ _ _).2]; rfl⟩,
      h4⟩

/-! ## OFB -/

theorem ofb_finalOk (c : Core) : FinalOk c (Mode.ofb c.bw) :=
  ⟨rfl, rfl, fun o ho => by
    have b := blk_bounds (c := c) (st := (Mode.ofb c.bw).step) rfl
    exact append_ok (copyBlk_inBounds (b _) (b _)) (xorBlk_inBounds (b _) (b _) (b _)) o ho,
    append_ok (copyBlk_wordAl _ _ _) (xorBlk_wordAl _ _ _ _)⟩

/-- OFB of the `len` bytes at `D`, as a final function leaves them: its
`n = len / L` whole blocks as `Spec.Ofb.crypt`'s from `iv`, then its last
`len % L` bytes XORed with `CIPH_K(Oₙ)`, `Oₙ` the last whole output block
(`Spec.Ofb.next` after `n`): `Spec.Ofb.cryptFinal`. -/
theorem ofbFinal_out {L : Nat} (hL : 0 < L) {ciph : Spec.Cbc.Cipher} (hc : ∀ b, (ciph b).length = L)
    (m₀ : Mem) (D : Addr) (iv : List Byte) (len : Nat) :
    (Spec.Ofb.crypt ciph iv (chunksAt L m₀ D (len / L))).flatten ++
        Spec.Cbc.xor (bytesAt m₀ (D + BitVec.ofNat 64 (L * (len / L))) (len % L))
          (ciph (Spec.Ofb.next ciph iv (len / L))) =
      Spec.Ofb.cryptFinal ciph L iv (bytesAt m₀ D len) := by
  rw [show chunksAt L m₀ D (len / L) = Proof.Modes.blocksOf L m₀ D (len / L) from rfl]
  have hx := Proof.Modes.xor_flatten_outputs hc m₀ (len / L) D iv
  have hnB : (Proof.Modes.blocksOf L m₀ D (len / L)).length = len / L := by simp [Proof.Modes.blocksOf]
  rw [Spec.Ofb.cryptFinal, Proof.Modes.bytesAt_length, Proof.Modes.blockCount_eq hL,
    Proof.Modes.bytesAt_blocks_tail L m₀ D len, Spec.Ofb.crypt, hnB]
  split
  · rename_i h0
    rw [h0, ← hx]
    simp [bytesAt, Spec.Cbc.xor]
  · rw [Proof.AesOfb.outputs_succ, List.flatten_append, List.flatten_singleton, ← hx]
    exact (List.zipWith_append (by
      rw [← Proof.Modes.bytesAt_mul, Proof.Modes.bytesAt_length, Proof.Modes.length_flatten_outputs hc])).symm

/-- OFB of a message's last piece, as the specification's. -/
theorem ofbFinal_wp (cs : CoreSpec c) {s₀ : State} {k : cs.Key} (hp : SeqPre c byteMode s₀)
    (hk : cs.KeyArgs s₀ (wrs0 c byteMode s₀) k) :
    WP isa (c.seqFinal (Mode.ofb c.bw)) s₀ fun s' => abiPreserved s₀ s' ∧
      Spec.Ofb.CryptFinal (cs.cipher k) (4 * c.bw) s₀.mem s'.mem (P s₀) (Dp s₀) (N s₀) ∧
      Changes c byteMode s₀ s' :=
  WP.mono (seqFinal_wp cs (ofb_finalOk c) (ofb_computes (cs.cipher_len k)) hp hk)
    fun s' ⟨h1, h2, h3, h4⟩ => by
      have hL0 : 0 < 4 * c.bw := by rcases hp.layout.bw with h | h <;> omega
      obtain ⟨e1, e2⟩ := ofb_run (cs.cipher k) (iv0 c s₀) (xsF c s₀)
      rw [chunksAt_length] at e2
      refine ⟨h1, ⟨?_, ?_⟩, h4⟩
      · rw [h2, finalOut, ← e1, ← e2]
        exact ofbFinal_out hL0 (cs.cipher_len k) s₀.mem (Dp s₀) (iv0 c s₀) (N s₀)
      · rw [h3, finalNext, ← e2, Proof.Modes.blockCount_eq hL0]
        split
        · rfl
        · exact (Proof.AesOfb.next_succ _ _ _).symm

end VG.Proof.Modes.RISCV64
