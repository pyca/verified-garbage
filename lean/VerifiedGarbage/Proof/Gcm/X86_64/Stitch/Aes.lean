module

import VerifiedGarbage.Proof.Gcm.X86_64.Stitch.Base
public import VerifiedGarbage.Proof.Aes.X86_64.Vaes.Ctr32
public import VerifiedGarbage.Impl.Gcm.X86_64.Stitch
public import VerifiedGarbage.Proof.Gcm.X86_64.Stitch.Spec
public import VerifiedGarbage.Proof.Gcm.X86_64.Stitch.SpecTo
public import VerifiedGarbage.Proof.Gcm.X86_64.Rev
import VerifiedGarbage.Proof.Gcm.X86_64.StitchTo.Base
import VerifiedGarbage.Proof.Gcm.X86_64.StitchZTo.Base
import VerifiedGarbage.Proof.Gcm.X86_64.Pclmul.Exec
import VerifiedGarbage.Proof.Framework.X86_64.Avx
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Aes.X86_64.Vaes.Rounds
import VerifiedGarbage.Proof.Aes.X86_64.CodeLit
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Taint

/-!
# Interleaved counter mode and GHASH: a batch of eight blocks

`batchM_ok`: `batch j g ix` encrypts the eight data blocks at `rdx + 32 j`
(blocks `c … c + 7`, `AInvM`) into the output: the counter blocks into
`ymm3`–`ymm6` (`Vaes.ctrs_ok`), AES of both lanes of each (`Vaes.aesG_ok`),
and the XOR of the data into the output (`xorDataKM_ok`). The blocks `g i`
between the rounds do what `Q` says, which neither the counter blocks, the
rounds nor the XOR (which writes only those eight output blocks) undo.

The output is the data itself, in place, or, out of place (`ix`), the buffer
at `r10` (`wAddr`), with `r8` holding its distance from the data: one proof
for both, from what both starts give (`LPre`: `SPre.toM`, `SPreTo.toM`).
Each pair of blocks is read before it is written, and written apart from the
pairs read after it, whichever the output (`xorDataKM_ok`). `batch_ok` is the
in-place case, for `AInv`.
-/

@[expose] public section

namespace VG.Proof.Gcm.X86_64.Stitch

open VG VG.X86_64
open VG.Impl.Aes.X86_64.Vaes (ctrsK aesK)
open VG.Impl.Gcm.X86_64.Stitch (aregs batch dstK srcK xorDataKM)
open VG.Proof.Aes.X86_64.Vaes (ctrs_ok aesG_ok xorData_ok two YFrame.of_keys)
open VG.Proof.Aes.X86_64.AesNi (Keys aesWith_eq blockAt_frame st)
open VG.Spec.Gcm (Block blockAt inc32 aesWith)

/-- The encryption after `c` blocks: the counter pair, the mask, the increment,
the key schedule and its last round key, and the data (blocks below `c`
encrypted, the others as they were). -/
structure AInv (s₀ : State) (c : Nat) (s : State) : Prop where
  le : c ≤ nb s₀
  ctr : ∀ l < 2, s.lane .xmm14 l = Nat.repeat inc32 (c + l) (cb s₀)
  msk : ∀ l < 2, s.lane .xmm0 l = revMask
  inc : ∀ l < 2, s.lane .xmm15 l = two
  rdi : s.gpr .rdi = kp s₀
  rsi : s.gpr .rsi = s₀.gpr .rsi
  r10 : s.gpr .r10 = kp s₀ + BitVec.ofNat 64 (16 * nr s₀)
  frame : Frame [dR s₀, pR s₀] s₀.mem s.mem
  blocks : ∀ k < nb s₀, blockAt s.mem (bAddr s₀ k) = if k < c then ctb s₀ k else blk s₀ k
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem AInv.yframe {s₀ : State} {c : Nat} {s s' : State} {rs : List XReg} (h : AInv s₀ c s)
    (f : YFrame rs s s') (h14 : .xmm14 ∉ rs) (h0 : .xmm0 ∉ rs) (h15 : .xmm15 ∉ rs) : AInv s₀ c s' :=
  ⟨h.le, fun l hl => by rw [f.lane _ h14 l hl]; exact h.ctr l hl, fun l hl => by rw [f.lane _ h0 l hl]; exact h.msk l hl,
    fun l hl => by rw [f.lane _ h15 l hl]; exact h.inc l hl, by rw [f.gpr]; exact h.rdi, by rw [f.gpr]; exact h.rsi,
    by rw [f.gpr]; exact h.r10, by rw [f.mem]; exact h.frame, fun k hk => by rw [f.mem]; exact h.blocks k hk,
    by rw [f.rd]; exact h.rd, by rw [f.wr]; exact h.wr⟩

/-! ## In place or out of place -/

section
variable (ix : Bool) (s₀ : State)

/-- Where the output goes: over the data, or, out of place (`ix`), to the
buffer at `r10`. -/
abbrev wp : Addr := if ix then op s₀ else dp s₀
abbrev wR : Region := ⟨wp ix s₀, 16 * nb s₀⟩
/-- Output block `k`. -/
abbrev wAddr (k : Nat) : Addr := wp ix s₀ + BitVec.ofNat 64 (16 * k)

end

/-- What the loops need of their start, in place (`SPre.toM`) or out of
place (`SPreTo.toM`). -/
structure LPre (ix : Bool) (s₀ : State) : Prop where
  rounds : nr s₀ = 10 ∨ nr s₀ = 12 ∨ nr s₀ = 14
  k_in : InRegions (s₀.rd ++ s₀.wr) (kp s₀) 256
  c_in : InRegions s₀.wr (cp s₀) 16
  y_in : InRegions s₀.wr (yp s₀) 16
  d_in : InRegions (s₀.rd ++ s₀.wr) (dp s₀) (16 * nb s₀)
  w_in : InRegions s₀.wr (wp ix s₀) (16 * nb s₀)
  p_in : InRegions s₀.wr (pp s₀) 1024
  w_k : (wR ix s₀).Disjoint (kR s₀)
  w_c : (wR ix s₀).Disjoint (cR s₀)
  w_y : (wR ix s₀).Disjoint (yR s₀)
  w_p : (wR ix s₀).Disjoint (pR s₀)
  p_k : (pR s₀).Disjoint (kR s₀)
  p_c : (pR s₀).Disjoint (cR s₀)
  p_y : (pR s₀).Disjoint (yR s₀)
  c_y : (cR s₀).Disjoint (yR s₀)
  d_p : (dR s₀).Disjoint (pR s₀)
  /-- Out of place, the output is apart from the data. -/
  d_w : ix = true → (dR s₀).Disjoint (wR ix s₀)
  wrap_d : (dp s₀).toNat + 16 * nb s₀ ≤ 2 ^ 64
  wrap_w : (wp ix s₀).toNat + 16 * nb s₀ ≤ 2 ^ 64
  wrap_k : (kp s₀).toNat + 256 ≤ 2 ^ 64
  wrap_p : (pp s₀).toNat + 1024 ≤ 2 ^ 64

theorem SPre.toM {s₀ : State} {lo : Nat} (hp : SPre s₀ lo) : LPre false s₀ where
  rounds := hp.rounds
  k_in := hp.k_in
  c_in := hp.c_in
  y_in := hp.y_in
  d_in := in_rdwr hp.d_in
  w_in := hp.d_in
  p_in := hp.p_in
  w_k := hp.d_k
  w_c := hp.d_c
  w_y := hp.d_y
  w_p := hp.d_p
  p_k := hp.p_k
  p_c := hp.p_c
  p_y := hp.p_y
  c_y := hp.c_y
  d_p := hp.d_p
  d_w := fun h => absurd h (by decide)
  wrap_d := hp.wrap_d
  wrap_w := hp.wrap_d
  wrap_k := hp.wrap_k
  wrap_p := hp.wrap_p

theorem SPreTo.toM {M : CtxMode} {s₀ : State} (hp : SPreTo M s₀) : LPre true s₀ where
  rounds := hp.rounds
  k_in := StitchZTo.inRegions_prefix hp.k_in M.ge
  c_in := hp.c_in
  y_in := hp.y_in
  d_in := hp.s_in
  w_in := hp.o_in
  p_in := hp.p_in
  w_k := hp.k_o.symm.sub_right (Region.sub_prefix M.ge)
  w_c := hp.o_c
  w_y := hp.o_y
  w_p := hp.o_p
  p_k := hp.k_p.symm.sub_right (Region.sub_prefix M.ge)
  p_c := hp.p_c
  p_y := hp.p_y
  c_y := hp.c_y
  d_p := hp.s_p
  d_w := fun _ => hp.s_o
  wrap_d := hp.wrap_s
  wrap_w := hp.wrap_o
  wrap_k := by
    have := hp.wrap_k; have := M.ge
    show (kp s₀).toNat + 256 ≤ 2 ^ 64; omega
  wrap_p := hp.wrap_p

/-- The key schedule is not in the output or the working space. -/
theorem sch_frameM {ix : Bool} {s₀ : State} (hp : LPre ix s₀) {m : Mem}
    (hf : Frame [wR ix s₀, pR s₀] s₀.mem m) :
    Spec.Aes.bytesAt m (kp s₀) (16 * (nr s₀ + 1)) = sch s₀ := by
  have hn : 16 * (nr s₀ + 1) ≤ 256 := by rcases hp.rounds with h | h | h <;> omega
  simp only [sch, Spec.Aes.bytesAt]
  refine List.map_congr_left fun i hi => ?_
  simp only [List.mem_range] at hi
  refine hf.bytes (R := ⟨kp s₀, 16 * (nr s₀ + 1)⟩) (fun r hr => ?_)
    (by show 16 * (nr s₀ + 1) ≤ 2 ^ 64; omega) hi
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact hp.w_k.symm.sub_left (Region.sub_prefix hn)
  · exact hp.p_k.symm.sub_left (Region.sub_prefix hn)

/-- The key schedule is not in the data or the working space. -/
theorem sch_frame {s₀ : State} {lo : Nat} (hp : SPre s₀ lo) {m : Mem} (hf : Frame [dR s₀, pR s₀] s₀.mem m) :
    Spec.Aes.bytesAt m (kp s₀) (16 * (nr s₀ + 1)) = sch s₀ :=
  sch_frameM hp.toM hf

/-- `AInv`, in place or out of place: the output blocks below `c` written,
and the data blocks from `c` on as they were. -/
structure AInvM (ix : Bool) (s₀ : State) (c : Nat) (s : State) : Prop where
  le : c ≤ nb s₀
  ctr : ∀ l < 2, s.lane .xmm14 l = Nat.repeat inc32 (c + l) (cb s₀)
  msk : ∀ l < 2, s.lane .xmm0 l = revMask
  inc : ∀ l < 2, s.lane .xmm15 l = two
  rdi : s.gpr .rdi = kp s₀
  rsi : s.gpr .rsi = s₀.gpr .rsi
  r10 : s.gpr .r10 = kp s₀ + BitVec.ofNat 64 (16 * nr s₀)
  frame : Frame [wR ix s₀, pR s₀] s₀.mem s.mem
  out : ∀ k < c, blockAt s.mem (wAddr ix s₀ k) = ctb s₀ k
  src : ∀ k < nb s₀, c ≤ k → blockAt s.mem (bAddr s₀ k) = blk s₀ k
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem AInv.toM {s₀ : State} {c : Nat} {s : State} (h : AInv s₀ c s) : AInvM false s₀ c s :=
  ⟨h.le, h.ctr, h.msk, h.inc, h.rdi, h.rsi, h.r10, h.frame,
    fun k hk => (h.blocks k (by have := h.le; omega)).trans (by simp only [hk, ite_true]),
    fun k hk hc => (h.blocks k hk).trans (by simp only [show ¬ k < c by omega, ite_false]), h.rd, h.wr⟩

theorem AInvM.toAInv {s₀ : State} {c : Nat} {s : State} (h : AInvM false s₀ c s) : AInv s₀ c s :=
  ⟨h.le, h.ctr, h.msk, h.inc, h.rdi, h.rsi, h.r10, h.frame, fun k hk => by
    by_cases hc : k < c
    · simp only [hc, ite_true]; exact h.out k hc
    · simp only [hc, ite_false]; exact h.src k hk (by omega), h.rd, h.wr⟩

theorem AInvM.yframe {ix : Bool} {s₀ : State} {c : Nat} {s s' : State} {rs : List XReg} (h : AInvM ix s₀ c s)
    (f : YFrame rs s s') (h14 : .xmm14 ∉ rs) (h0 : .xmm0 ∉ rs) (h15 : .xmm15 ∉ rs) : AInvM ix s₀ c s' :=
  ⟨h.le, fun l hl => by rw [f.lane _ h14 l hl]; exact h.ctr l hl, fun l hl => by rw [f.lane _ h0 l hl]; exact h.msk l hl,
    fun l hl => by rw [f.lane _ h15 l hl]; exact h.inc l hl, by rw [f.gpr]; exact h.rdi, by rw [f.gpr]; exact h.rsi,
    by rw [f.gpr]; exact h.r10, by rw [f.mem]; exact h.frame,
    fun k hk => by rw [f.mem]; exact h.out k hk, fun k hk hc => by rw [f.mem]; exact h.src k hk hc,
    by rw [f.rd]; exact h.rd, by rw [f.wr]; exact h.wr⟩

theorem AInvM.keys {ix : Bool} {s₀ : State} (hp : LPre ix s₀) {c : Nat} {s : State} (hI : AInvM ix s₀ c s) :
    Keys (nr s₀) (sch s₀) s :=
  ⟨by rw [hI.rdi, sch_frameM hp hI.frame], by rcases hp.rounds with h | h | h <;> omega,
    fun j hj => by
      rw [hI.rd, hI.wr, hI.rdi]
      exact in_sub_int hp.k_in (by rcases hp.rounds with h | h | h <;> omega)⟩

theorem AInv.keys {s₀ : State} (hp : SPre s₀) {c : Nat} {s : State} (hI : AInv s₀ c s) :
    Keys (nr s₀) (sch s₀) s :=
  hI.toM.keys hp.toM

/-- Addresses at offsets of two bases, equal as numbers. -/
theorem addr_eq {a b : Addr} {x y : Nat} (h : a.toNat + x = b.toNat + y) :
    a + BitVec.ofNat 64 x = b + BitVec.ofNat 64 y := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.add_mod_mod,
    Nat.add_mod_mod, h]

theorem aregs_ok : aregs.Nodup ∧ .xmm13 ∉ aregs ∧ ∀ r ∈ aregs, r ≠ .xmm14 ∧ r ≠ .xmm0 ∧ r ≠ .xmm15 := by decide

/-! ## The XOR into the output -/

/-- Where `dstK ix` stores and `srcK ix` loads: `rdx`, or, out of place,
`rdx + r8`. -/
def oA (s : State) (ix : Bool) : Addr := if ix then s.gpr .rdx + s.gpr .r8 else s.gpr .rdx

theorem oA_congr {s s' : State} (ix : Bool) (h : s'.gpr = s.gpr) : oA s' ix = oA s ix := by
  simp only [oA, h]

theorem ea_dstK (s : State) (ix : Bool) (d : Nat) : s.ea (dstK ix d) = oA s ix + BitVec.ofInt 64 (d : Int) := by
  cases ix
  · exact VG.Proof.Gcm.X86_64.Pclmul.ea_at s .rdx d
  · exact StitchZTo.ea_atIx s .rdx .r8 d

/-- `srcK ld` loads from where `dstK ld` stores. -/
theorem ea_srcK (s : State) (ld : Bool) (d : Nat) : s.ea (srcK ld d) = oA s ld + BitVec.ofInt 64 (d : Int) := by
  cases ld
  · exact VG.Proof.Gcm.X86_64.Pclmul.ea_at s .rdx d
  · exact StitchZTo.ea_atIx s .rdx .r8 d

/-- XOR the two lanes of `b` into the blocks read at `srcK ld d` and the next,
and store them to `dstK ix d`. -/
theorem xor1M_ok (ix ld : Bool) (t : XReg) (b : XReg) (d : Nat) (s : State) (hb8 : b ≠ t)
    (hinS : InRegions (s.rd ++ s.wr) (oA s ld + BitVec.ofInt 64 (d : Int)) 32)
    (hin : InRegions s.wr (oA s ix + BitVec.ofInt 64 (d : Int)) 32) :
    WP isa (.block [.vmovdquLoad .l256 t (srcK ld d), .vop (.vbin .vpxor .l256 b b t),
        .vmovdquStore .l256 (dstK ix d) b]) s fun s' =>
      (∃ v : BitVec 256, s'.mem = s.mem.writeW (oA s ix + BitVec.ofInt 64 (d : Int)) v) ∧
      (∀ l < 2, blockAt s'.mem (oA s ix + BitVec.ofInt 64 (d : Int) + BitVec.ofNat 64 (16 * l)) =
        blockAt s.mem (oA s ld + BitVec.ofInt 64 (d : Int) + BitVec.ofNat 64 (16 * l)) ^^^
          XBinOp.eval .pshufb (s.lane b l) revMask) ∧
      s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ r, r ≠ b → r ≠ t → ∀ l < 2, s'.lane r l = s.lane r l) := by
  let a := oA s ix + BitVec.ofInt 64 (d : Int)
  let as := oA s ld + BitVec.ofInt 64 (d : Int)
  let v := s.mem.readW as 256
  let s₁ := s.setV .l256 t (v.extractLsb' 0 128) (v.extractLsb' 128 128)
  let s₂ := (VOp.vbin .vpxor .l256 b b t).exec s₁
  have l₁ : ∀ l < 2, s₁.lane t l = s.mem.readW (as + BitVec.ofNat 64 (16 * l)) 128 := fun l hl => by
    rw [← StitchTo.load256_lane _ _ hl]
    rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl <;> simp [s₁, State.lane_setV256, v]
  rw [WP.block_cons_iff]
  refine ⟨s₁, by
    simp only [isa, exec, State.load256, ea_srcK, hinS, ite_true, Option.map_some]; rfl, ?_⟩
  rw [WP.block_cons_iff]; refine ⟨s₂, rfl, ?_⟩
  rw [WP.block_cons_iff]
  have hg₂ : s₂.gpr = s.gpr := by simp [s₂, s₁]
  have hst : isa.exec (.vmovdquStore .l256 (dstK ix d) b) s₂ =
      some (s₂.setMem (s.mem.writeW a (s₂.ymm b))) := by
    simp only [isa, exec, State.store256_eq, ea_dstK, oA_congr ix hg₂, s₂, s₁,
      VOp.exec_wr, State.setV_wr, VOp.exec_mem, State.setV_mem, hin, ite_true, a]
  refine ⟨_, hst, WP.block_nil ?_⟩
  have z₂ : ∀ l < 2, s₂.lane b l = s.lane b l ^^^ s.mem.readW (as + BitVec.ofNat 64 (16 * l)) 128 :=
    fun l hl => by
      simp only [s₂, lane_vbin256, ite_true, VBinOp.sse, ← l₁ l hl]
      rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl <;>
        simp [s₁, State.lane_setV256, hb8, VG.Proof.Aes.X86_64.AesNi.eval_pxor]
  refine ⟨⟨_, rfl⟩, fun l hl => ?_, by simp [s₂, s₁], by simp [s₂, s₁], by simp [s₂, s₁], fun r h1 h2 l hl => ?_⟩
  · simp only [State.setMem_mem]
    rw [StitchTo.blockAt_writeW_lane2 _ _ _ hl, StitchTo.ymm_lane2 _ _ hl, z₂ l hl,
      VG.Proof.Gcm.X86_64.pshufb_rev_xor, BitVec.xor_comm, ← VG.Proof.Gcm.X86_64.blockAt_eq]
  · simp [s₂, s₁, lane_vbin256, State.lane_setV256, h1, h2]

/-- `xorDataKM ix t ld regs j`: the pairs of blocks read at `oA ld + 32 (j + k)`,
each XORed with the lanes of register `k` and written at
`oA + 32 (j + k)`, for an output each pair of which is apart from the pairs
read after it. -/
theorem xorDataKM_ok (ix ld : Bool) (t : XReg) (regs : List XReg) (j : Nat) (s : State) (hnd : regs.Nodup)
    (h8 : t ∉ regs)
    (hinS : ∀ k < regs.length,
      InRegions (s.rd ++ s.wr) (oA s ld + BitVec.ofInt 64 ((32 * (j + k) : Nat) : Int)) 32)
    (hin : ∀ k < regs.length, InRegions s.wr (oA s ix + BitVec.ofInt 64 ((32 * (j + k) : Nat) : Int)) 32)
    (hsep : ∀ a b, a < b → b < regs.length → ∀ l < 2,
      Region.Disjoint ⟨oA s ld + BitVec.ofNat 64 (16 * (2 * (j + b) + l)), 16⟩
        ⟨oA s ix + BitVec.ofNat 64 (32 * (j + a)), 32⟩)
    (hw : 32 * (j + regs.length) ≤ 2 ^ 64) :
    WP isa (.block (xorDataKM ix t ld regs j)) s fun s' =>
      (∀ k (h : k < regs.length), ∀ l < 2,
        blockAt s'.mem (oA s ix + BitVec.ofNat 64 (16 * (2 * (j + k) + l))) =
          blockAt s.mem (oA s ld + BitVec.ofNat 64 (16 * (2 * (j + k) + l))) ^^^
            XBinOp.eval .pshufb (s.lane regs[k] l) revMask) ∧
      Frame [⟨oA s ix + BitVec.ofNat 64 (32 * j), 32 * regs.length⟩] s.mem s'.mem ∧
      s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ r, r ≠ t → r ∉ regs → ∀ l < 2, s'.lane r l = s.lane r l) := by
  induction regs generalizing j s with
  | nil => exact WP.block_nil ⟨fun _ h => absurd h (by simp), Frame.refl _ _, rfl, rfl, rfl,
      fun _ _ _ _ _ => rfl⟩
  | cons b bs ih =>
    have hb8 : b ≠ t := fun h => h8 (h ▸ List.mem_cons_self)
    have hbs : b ∉ bs := (List.nodup_cons.mp hnd).1
    have h8' : t ∉ bs := fun h => h8 (List.mem_cons_of_mem _ h)
    simp only [List.length_cons] at hinS hin hsep hw
    rw [xorDataKM, WP.block_append_iff]
    have hin0 := hin 0 (by omega)
    have hinS0 := hinS 0 (by omega)
    rw [Nat.add_zero] at hin0 hinS0
    refine WP.mono (xor1M_ok ix ld t b (32 * j) s hb8 hinS0 hin0) fun s₁ ⟨⟨v, m₁⟩, b₁, g₁, rd₁, wr₁, x₁⟩ => ?_
    have o₁ : oA s₁ ix = oA s ix := oA_congr ix g₁
    have i₁ : oA s₁ ld = oA s ld := oA_congr ld g₁
    refine WP.mono (ih (j + 1) s₁ (List.nodup_cons.mp hnd).2 h8'
      (fun k hk => by
        rw [rd₁, wr₁, i₁, show j + 1 + k = j + (k + 1) by omega]; exact hinS (k + 1) (by omega))
      (fun k hk => by
        rw [wr₁, o₁, show j + 1 + k = j + (k + 1) by omega]; exact hin (k + 1) (by omega))
      (fun a c hac hc l hl => by
        rw [i₁, o₁, show j + 1 + a = j + (a + 1) by omega, show j + 1 + c = j + (c + 1) by omega]
        exact hsep (a + 1) (c + 1) (by omega) (by omega) l hl)
      (by omega)) fun s' ⟨hb, hf, g, rd, wr, hx⟩ => ?_
    rw [i₁, o₁] at hb
    rw [o₁] at hf
    rw [VG.Proof.Aes.X86_64.AesNi.ofInt_natCast] at m₁ b₁
    have adr : ∀ (p : Addr), ∀ l < 2, p + BitVec.ofNat 64 (16 * (2 * j + l)) =
        p + BitVec.ofNat 64 (32 * j) + BitVec.ofNat 64 (16 * l) := fun p l _ => by
      rw [BitVec.add_assoc, ← BitVec.ofNat_add, show 32 * j + 16 * l = 16 * (2 * j + l) by omega]
    have hdj : ∀ l < 2, ∀ r ∈ [(⟨oA s ix + BitVec.ofNat 64 (32 * (j + 1)), 32 * bs.length⟩ : Region)],
        Region.Disjoint ⟨oA s ix + BitVec.ofNat 64 (16 * (2 * j + l)), 16⟩ r := by
      intro l hl
      simp only [List.mem_singleton, forall_eq]
      exact Offset.disjoint _ (by omega) (by omega) (by omega)
    refine ⟨fun k hk l hl => ?_, ?_, g.trans g₁, rd.trans rd₁, wr.trans wr₁, fun r hr hr' l hl => ?_⟩
    · cases k with
      | zero =>
        simp only [List.getElem_cons_zero, Nat.add_zero]
        rw [blockAt_frame hf (hdj l hl), adr _ l hl, b₁ l hl, adr _ l hl]
      | succ k =>
        simp only [List.getElem_cons_succ]
        have hk' : k < bs.length := by simpa using hk
        have hd := hsep 0 (k + 1) (by omega) (by omega) l hl
        rw [Nat.add_zero] at hd
        rw [show j + (k + 1) = j + 1 + k by omega, hb k hk' l hl, m₁,
          StitchZTo.blockAt_writeW_out (R := ⟨oA s ix + BitVec.ofNat 64 (32 * j), 32⟩) (by
            rw [show j + 1 + k = j + (k + 1) by omega]; exact hd) rfl,
          x₁ _ (fun h => hbs (h ▸ List.getElem_mem hk')) (fun h => h8' (h ▸ List.getElem_mem hk')) l hl]
    · rw [m₁] at hf
      refine (Frame.writeW (Frame.refl [⟨oA s ix + BitVec.ofNat 64 (32 * j), 32 * (bs.length + 1)⟩]
        s.mem) List.mem_cons_self _ (by simp only [Region.Contains, BitVec.sub_self]; simp; omega)).trans
        (hf.sub fun r hr => ⟨_, List.mem_cons_self, fun a ha => ?_⟩)
      simp only [List.mem_singleton] at hr
      subst hr
      exact Offset.sub _ (by omega) (by omega) a ha
    · simp only [List.mem_cons, not_or] at hr'
      rw [hx r hr hr'.2 l hl, x₁ r hr'.1 hr l hl]

/-! ## A batch -/

theorem batchM_ok {ix st ld : Bool} {s₀ : State} (hp : LPre ix s₀) (hst : st = (ix && !ld)) (hld : ld = true → ix = true)
    (g : Nat → List Instr) (G : List XReg)
    (hG : ∀ r ∈ G, r ≠ .xmm13 ∧ r ∉ aregs ∧ r ≠ .xmm14 ∧ r ≠ .xmm0 ∧ r ≠ .xmm15)
    (Q : Nat → State → Prop)
    (hg : ∀ j, 1 ≤ j → j ≤ 9 → ∀ s, Keys (nr s₀) (sch s₀) s → Q j s →
      WP isa (.block (g j)) s fun s' => Q (j + 1) s' ∧ YFrame G s s')
    (hq : ∀ j s s', Q j s → YFrame (.xmm13 :: .xmm14 :: aregs) s s' → Q j s')
    {c j : Nat}
    (hqx : ∀ s s', Q 10 s → s'.gpr = s.gpr → s'.rd = s.rd → s'.wr = s.wr →
      (∀ r, r ≠ .xmm13 → r ∉ aregs → ∀ l < 2, s'.lane r l = s.lane r l) →
      Frame [⟨wAddr ix s₀ c, 128⟩] s.mem s'.mem → Q 10 s')
    (hc : c + 8 ≤ nb s₀) {s : State} (hI : AInvM ix s₀ c s)
    (hr8 : ix = true → s.gpr .r8 = if ld then dp s₀ - op s₀ else op s₀ - dp s₀)
    (hrdx : (s.gpr .rdx).toNat + 32 * j = (if ld then op s₀ else dp s₀).toNat + 16 * c) (hQ : Q 1 s) :
    WP isa (batch j g st ld) s fun s' => AInvM ix s₀ (c + 8) s' ∧ Q 10 s' ∧ s'.gpr = s.gpr ∧
      (∀ r, r ≠ .xmm13 → r ≠ .xmm14 → r ∉ aregs → r ∉ G → ∀ l < 2, s'.lane r l = s.lane r l) ∧
      Frame [⟨wAddr ix s₀ c, 128⟩] s.mem s'.mem := by
  obtain ⟨hnd, h13, hx⟩ := aregs_ok
  have hw := hp.wrap_w
  have hwd := hp.wrap_d
  refine WP.seq (WP.mono (ctrs_ok .xmm14 .xmm0 .xmm15 (by decide) (by decide) aregs s (cb s₀) c hnd hx
    hI.ctr hI.msk hI.inc) fun s₁ ⟨e₁, c₁, f₁⟩ => ?_)
  have hK₁ : Keys (nr s₀) (sch s₀) s₁ := YFrame.of_keys (hI.keys hp) f₁
  have hQ₁ : Q 1 s₁ := hq _ _ _ hQ (f₁.mono fun r hr => List.mem_cons_of_mem _ hr)
  refine WP.seq (WP.mono (aesG_ok .xmm13 aregs hnd h13 hp.rounds g G (fun r h => ⟨(hG r h).1, (hG r h).2.1⟩) Q
    hg (fun j s s' h f => hq j s s' h (f.mono fun r hr => by
      rcases List.mem_cons.mp hr with rfl | hr
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hr))) s₁ hK₁ hQ₁
    (by rw [f₁.gpr, hI.rsi]; simp)
    (by rw [f₁.gpr, hI.r10, hI.rdi])) fun s₂ ⟨e₂, hQ₂, f₂⟩ => ?_)
  -- The keystream blocks.
  have ks : ∀ k (h : k < aregs.length), ∀ l < 2, XBinOp.eval .pshufb (s₂.lane aregs[k] l) revMask =
      ciph s₀ (Nat.repeat inc32 (c + 2 * k + l) (cb s₀)) := fun k h l hl =>
    (aesWith_eq _ _ _ _ (by rw [e₂ _ (List.getElem_mem h) l hl, e₁ k h l hl])).symm
  have hg₂ : s₂.gpr = s.gpr := by rw [f₂.gpr, f₁.gpr]
  have hwr : (if ld then op s₀ else dp s₀).toNat + 16 * nb s₀ ≤ 2 ^ 64 := by
    cases ld
    · exact hwd
    · obtain rfl := hld rfl; exact hw
  -- Where `rdx` points: at the data, or, out of place (`ld`), at the output.
  have raddr : ∀ i, s.gpr .rdx + BitVec.ofNat 64 (32 * j + 16 * i) =
      (if ld then op s₀ else dp s₀) + BitVec.ofNat 64 (16 * (c + i)) := fun i => addr_eq (by omega)
  -- Where the pairs are read from.
  have addr : ∀ i, oA s ld + BitVec.ofNat 64 (32 * j + 16 * i) = bAddr s₀ (c + i) := fun i => by
    cases ld
    · exact raddr i
    · show s.gpr .rdx + s.gpr .r8 + _ = dp s₀ + _
      rw [hr8 (hld rfl)]
      exact StitchZTo.src_addr (raddr i)
  -- Where the output pairs go.
  have oaddr : ∀ i, oA s st + BitVec.ofNat 64 (32 * j + 16 * i) = wAddr ix s₀ (c + i) := fun i => by
    subst hst
    cases ix <;> cases ld
    · exact raddr i
    · exact absurd (hld rfl) (by decide)
    · show s.gpr .rdx + s.gpr .r8 + _ = op s₀ + _
      rw [hr8 rfl]
      exact StitchZTo.src_addr (raddr i)
    · exact raddr i
  have e32 : ∀ k, BitVec.ofInt 64 ((32 * (j + k) : Nat) : Int) = BitVec.ofNat 64 (32 * j + 16 * (2 * k)) :=
    fun k => by rw [BitVec.ofInt_natCast]; congr 1; omega
  have e16 : ∀ k l, 16 * (2 * (j + k) + l) = 32 * j + 16 * (2 * k + l) := fun k l => by omega
  have o₂ : oA s₂ st = oA s st := oA_congr st hg₂
  have i₂ : oA s₂ ld = oA s ld := oA_congr ld hg₂
  refine WP.mono (xorDataKM_ok st ld .xmm13 aregs j s₂ hnd h13
      (fun k hk => by
        rw [i₂, f₂.rd, f₁.rd, f₂.wr, f₁.wr, hI.rd, hI.wr, e32, addr]
        exact in_sub hp.d_in (by simp [aregs] at hk; omega))
      (fun k hk => by
        rw [o₂, f₂.wr, f₁.wr, hI.wr, e32, oaddr]
        exact in_sub hp.w_in (by simp [aregs] at hk; omega))
      (fun a b hab hb l hl => by
        rw [i₂, o₂, e16, show 32 * (j + a) = 32 * j + 16 * (2 * a) by omega, addr, oaddr]
        simp only [aregs, List.length_cons, List.length_nil] at hb
        cases ix
        · cases ld
          · exact Offset.disjoint _ (Or.inr (by omega)) (by omega) (by omega)
          · exact absurd (hld rfl) (by decide)
        · exact ((hp.d_w rfl).sub_left (Offset.sub_base _ (by omega))).sub_right
            (Offset.sub_base _ (by omega)))
      (by simp only [aregs, List.length_cons, List.length_nil]; omega))
    fun s₃ ⟨b₃, fr₃, g₃, rd₃, wr₃, x₃⟩ => ?_
  have hm₂ : s₂.mem = s.mem := by rw [f₂.mem, f₁.mem]
  rw [hm₂, i₂, o₂] at b₃
  rw [hm₂, o₂] at fr₃
  rw [show 32 * j = 32 * j + 16 * 0 by omega, oaddr, Nat.add_zero] at fr₃
  have hb3 : ∀ k (h : k < aregs.length), ∀ l < 2,
      blockAt s₃.mem (wAddr ix s₀ (c + (2 * k + l))) =
        blk s₀ (c + (2 * k + l)) ^^^ XBinOp.eval .pshufb (s₂.lane aregs[k] l) revMask :=
    fun k h l hl => by
      have := b₃ k h l hl
      rwa [e16, oaddr, addr, hI.src _ (by simp [aregs] at h; omega) (by omega)] at this
  have fr' : Frame [⟨wAddr ix s₀ c, 128⟩] s.mem s₃.mem := by simpa [aregs] using fr₃
  have kx : ∀ r, r ≠ .xmm13 → r ≠ .xmm14 → r ∉ aregs → r ∉ G → ∀ l < 2, s₃.lane r l = s.lane r l :=
    fun r h13' h14 hr hg' l hl => by
      rw [x₃ r h13' hr l hl, f₂.lane r (by simp [h13', hr, hg']) l hl, f₁.lane r (by simp [h14, hr]) l hl]
  have gs : s₃.gpr = s.gpr := by rw [g₃, hg₂]
  -- The output written is apart from the data still to read.
  have dsep : ∀ k < nb s₀, c + 8 ≤ k → ∀ r ∈ [(⟨wAddr ix s₀ c, 128⟩ : Region)],
      Region.Disjoint ⟨bAddr s₀ k, 16⟩ r := fun k hk hck r hr => by
    simp only [List.mem_singleton] at hr
    subst hr
    cases ix
    · intro a h₁ h₂
      exact VG.Proof.Aes.X86_64.AesNi.run_sep hwd hk hc (by omega) h₁ h₂
    · exact ((hp.d_w rfl).sub_left (Offset.sub_base _ (by omega))).sub_right (Offset.sub_base _ (by omega))
  refine ⟨⟨by omega, fun l hl => ?_, fun l hl => ?_, fun l hl => ?_, by rw [gs, hI.rdi],
    by rw [gs, hI.rsi], by rw [gs, hI.r10], ?_, ?_, ?_,
    by rw [rd₃, f₂.rd, f₁.rd, hI.rd], by rw [wr₃, f₂.wr, f₁.wr, hI.wr]⟩,
    hqx s₂ s₃ hQ₂ g₃ rd₃ wr₃ (fun r h1 h2 l hl => x₃ r h1 h2 l hl) (by rw [hm₂]; exact fr'),
    gs, kx, fr'⟩
  · rw [x₃ _ (by decide) (by decide) l hl, f₂.lane _ (by
      simp only [List.mem_cons, List.mem_append, not_or]
      exact ⟨by decide, by decide, fun h => (hG _ h).2.2.1 rfl⟩) l hl, c₁ l hl]
    simp [aregs]
  · rw [kx _ (by decide) (by decide) (by decide) (fun h => (hG _ h).2.2.2.1 rfl) l hl, hI.msk l hl]
  · rw [kx _ (by decide) (by decide) (by decide) (fun h => (hG _ h).2.2.2.2 rfl) l hl, hI.inc l hl]
  · -- The output written is only in the output.
    refine hI.frame.trans (fr'.sub fun r hr => ⟨wR ix s₀, List.mem_cons_self, fun a ha => ?_⟩)
    simp only [List.mem_singleton] at hr
    subst hr
    exact VG.Proof.Aes.X86_64.AesNi.run_in hw hc (n := 8) ha
  · intro k hk
    by_cases hlo : k < c
    · rw [blockAt_frame fr' fun r hr => by
        simp only [List.mem_singleton] at hr
        subst hr
        intro a h₁ h₂
        exact VG.Proof.Aes.X86_64.AesNi.run_sep hw (by omega) hc (by omega) h₁ h₂]
      exact hI.out k hlo
    · obtain ⟨i, rfl⟩ : ∃ i, k = c + (2 * (i / 2) + i % 2) := ⟨k - c, by omega⟩
      have hj : i / 2 < aregs.length := by simp [aregs]; omega
      rw [hb3 (i / 2) hj (i % 2) (by omega), ks (i / 2) hj (i % 2) (by omega),
        show c + 2 * (i / 2) + i % 2 = c + (2 * (i / 2) + i % 2) by omega]
  · intro k hk hck
    rw [blockAt_frame fr' (dsep k hk hck)]
    exact hI.src k hk (by omega)

theorem batch_ok {s₀ : State} (hp : SPre s₀) (g : Nat → List Instr) (G : List XReg)
    (hG : ∀ r ∈ G, r ≠ .xmm13 ∧ r ∉ aregs ∧ r ≠ .xmm14 ∧ r ≠ .xmm0 ∧ r ≠ .xmm15)
    (Q : Nat → State → Prop)
    (hg : ∀ j, 1 ≤ j → j ≤ 9 → ∀ s, Keys (nr s₀) (sch s₀) s → Q j s →
      WP isa (.block (g j)) s fun s' => Q (j + 1) s' ∧ YFrame G s s')
    (hq : ∀ j s s', Q j s → YFrame (.xmm13 :: .xmm14 :: aregs) s s' → Q j s')
    {c j : Nat}
    (hqx : ∀ s s', Q 10 s → s'.gpr = s.gpr → s'.rd = s.rd → s'.wr = s.wr →
      (∀ r, r ≠ .xmm13 → r ∉ aregs → ∀ l < 2, s'.lane r l = s.lane r l) →
      Frame [⟨bAddr s₀ c, 128⟩] s.mem s'.mem → Q 10 s')
    (hc : c + 8 ≤ nb s₀) {s : State} (hI : AInv s₀ c s)
    (hrdx : (s.gpr .rdx).toNat + 32 * j = (dp s₀).toNat + 16 * c) (hQ : Q 1 s) :
    WP isa (batch j g) s fun s' => AInv s₀ (c + 8) s' ∧ Q 10 s' ∧ s'.gpr = s.gpr ∧
      (∀ r, r ≠ .xmm13 → r ≠ .xmm14 → r ∉ aregs → r ∉ G → ∀ l < 2, s'.lane r l = s.lane r l) ∧
      Frame [⟨bAddr s₀ c, 128⟩] s.mem s'.mem :=
  WP.mono (batchM_ok (ld := false) hp.toM rfl (fun h => absurd h (by decide)) g G hG Q hg hq hqx hc hI.toM
    (fun h => absurd h (by decide)) hrdx hQ) fun _ ⟨hA, h⟩ => ⟨hA.toAInv, h⟩

end VG.Proof.Gcm.X86_64.Stitch
