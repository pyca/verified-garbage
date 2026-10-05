import VerifiedGarbage.Proof.Rc2.AArch64.Cbc.Verified
import VerifiedGarbage.Impl.Rc2.AArch64.Stream
import VerifiedGarbage.Proof.Rc2.AArch64.Block
import VerifiedGarbage.Spec.Rc2.Contract
import VerifiedGarbage.Proof.Rc2.Stream
import VerifiedGarbage.Proof.MdStream.AArch64.Words
import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.Rc2.AArch64.Key
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Rc2.Scratch
import VerifiedGarbage.Proof.Framework.AArch64.StackScratchWipe

/- Proofs formerly in `VerifiedGarbage.Proof.Rc2.AArch64.Stream.Lit`. -/
section

/-! # Literal streaming RC2-CBC programs

`init` and the update functions as literals (`materialize_code`), whose calls
refer to the literals of the key expansion and the CBC functions. -/

namespace VG

materialize_code Impl.Rc2.AArch64.Stream.init
materialize_code Impl.Rc2.AArch64.Stream.encryptUpdate
materialize_code Impl.Rc2.AArch64.Stream.decryptUpdate

end VG

end

/- Proofs formerly in `VerifiedGarbage.Proof.Rc2.AArch64.Stream.ConstantTime`. -/
section

/-! # Constant-time streaming RC2-CBC

The taint analysis of `init` and the update functions, the callees included,
from the public arguments: all seven (pointers and lengths), and the stack
pointer. -/

namespace VG.Proof.Rc2.AArch64.Stream

open VG VG.AArch64 VG.Impl.Rc2.AArch64.Stream

/-- The public registers: all seven arguments. -/
abbrev args : List Reg := [.x0, .x1, .x2, .x3, .x4, .x5, .x6]

theorem init_constantTime (pre : State → Prop) :
    ConstantTime isa pre (PublicRegs VG.Proof.Rc2.AArch64.Stream.args) init := by
  refine VG.Taint.constantTime (A := taint) (Taint.ofRegs VG.Proof.Rc2.AArch64.Stream.args) ?_ (by taint_decide)
  intro s₁ s₂ _ _ hp
  exact ⟨hp.1, fun r hr => hp.2 r (Taint.mem_ofRegs.mp hr)⟩

theorem encryptUpdate_constantTime (pre : State → Prop) :
    ConstantTime isa pre (PublicRegs VG.Proof.Rc2.AArch64.Stream.args) encryptUpdate := by
  refine VG.Taint.constantTime (A := taint) (Taint.ofRegs VG.Proof.Rc2.AArch64.Stream.args) ?_ (by taint_decide)
  intro s₁ s₂ _ _ hp
  exact ⟨hp.1, fun r hr => hp.2 r (Taint.mem_ofRegs.mp hr)⟩

theorem decryptUpdate_constantTime (pre : State → Prop) :
    ConstantTime isa pre (PublicRegs VG.Proof.Rc2.AArch64.Stream.args) decryptUpdate := by
  refine VG.Taint.constantTime (A := taint) (Taint.ofRegs VG.Proof.Rc2.AArch64.Stream.args) ?_ (by taint_decide)
  intro s₁ s₂ _ _ hp
  exact ⟨hp.1, fun r hr => hp.2 r (Taint.mem_ofRegs.mp hr)⟩

end VG.Proof.Rc2.AArch64.Stream

end

/- Proofs formerly in `VerifiedGarbage.Proof.Rc2.AArch64.Stream.Contract`. -/
section

/-! # Streaming RC2-CBC on AArch64: the contracts the proofs use

`Spec.Rc2.cbcInitContract` and `Spec.Rc2.cbcUpdateContract` spelled out for
AArch64 (the arguments in `x0`–`x6`), with the 16-byte frame below the stack
pointer that saves `x30` around the calls. -/

namespace VG.Proof.Rc2.AArch64.Stream

open VG VG.AArch64

/-- `init(key = x0, key_len = x1, effective_bits = x2, iv = x3, iv_len = x4,
ctx = x5, scratch = x6)`. -/
def initContract : Contract isa where
  pre s :=
    let key : Region := ⟨s.gpr .x0, (s.gpr .x1).toNat⟩
    let iv : Region := ⟨s.gpr .x3, (s.gpr .x4).toNat⟩
    let ctx : Region := ⟨s.gpr .x5, 144⟩
    let scr : Region := ⟨s.gpr .x6, 576⟩
    let stk : Region := ⟨s.sp - 16, 16⟩
    16 ≤ s.sp.toNat ∧ s.rd = [key, iv] ∧ s.wr = [ctx, scr] ∧
      key.Disjoint ctx ∧ key.Disjoint scr ∧ iv.Disjoint ctx ∧ iv.Disjoint scr ∧ ctx.Disjoint scr ∧
      stk.Disjoint key ∧ stk.Disjoint iv ∧ stk.Disjoint ctx ∧ stk.Disjoint scr ∧
      (s.gpr .x5).toNat + 144 ≤ 2 ^ 64 ∧ (s.gpr .x6).toNat + 576 ≤ 2 ^ 64
  post s s' :=
    ∀ direction, match Spec.Rc2.initWithEffectiveBits
        (Spec.Rc2.bytesAt s.mem (s.gpr .x0) (s.gpr .x1).toNat)
        (Spec.Rc2.bytesAt s.mem (s.gpr .x3) (s.gpr .x4).toNat) direction (s.gpr .x2).toNat with
      | .ok c => BitVec.setWidth 32 (s'.gpr .x0) = 0 ∧ Spec.Rc2.contextAt s'.mem (s.gpr .x5) direction 0 = c
      | .error e => (BitVec.setWidth 32 (s'.gpr .x0)).toNat = e.code
  pub := PublicRegs [.x0, .x1, .x2, .x3, .x4, .x5, .x6]

/-- `update(ctx = x0, pending_len = x1, data = x2, len = x3, out = x4,
out_len = x5, scratch = x6)` in the direction `d`. -/
def updateContract (d : Spec.Rc2.Direction) : Contract isa where
  pre s :=
    let ctx : Region := ⟨s.gpr .x0, 144⟩
    let data : Region := ⟨s.gpr .x2, (s.gpr .x3).toNat⟩
    let out : Region := ⟨s.gpr .x4, (s.gpr .x5).toNat⟩
    let scr : Region := ⟨s.gpr .x6, 576⟩
    let stk : Region := ⟨s.sp - 16, 16⟩
    16 ≤ s.sp.toNat ∧ s.rd = [data] ∧ s.wr = [ctx, out, scr] ∧
      ctx.Disjoint data ∧ ctx.Disjoint out ∧ ctx.Disjoint scr ∧ data.Disjoint out ∧
      data.Disjoint scr ∧ out.Disjoint scr ∧
      stk.Disjoint ctx ∧ stk.Disjoint data ∧ stk.Disjoint out ∧ stk.Disjoint scr ∧
      (s.gpr .x0).toNat + 144 ≤ 2 ^ 64 ∧ (s.gpr .x2).toNat + (s.gpr .x3).toNat ≤ 2 ^ 64 ∧
      (s.gpr .x4).toNat + (s.gpr .x5).toNat ≤ 2 ^ 64 ∧ (s.gpr .x6).toNat + 576 ≤ 2 ^ 64 ∧
      (s.gpr .x1).toNat < 8 ∧ (s.gpr .x5).toNat = ((s.gpr .x1).toNat + (s.gpr .x3).toNat) / 8 * 8
  post s s' :=
    let result := Spec.Rc2.update (Spec.Rc2.contextAt s.mem (s.gpr .x0) d (s.gpr .x1).toNat)
      (Spec.Rc2.bytesAt s.mem (s.gpr .x2) (s.gpr .x3).toNat)
    Spec.Rc2.contextAt s'.mem (s.gpr .x0) d (((s.gpr .x1).toNat + (s.gpr .x3).toNat) % 8) = result.1 ∧
      Spec.Rc2.bytesAt s'.mem (s.gpr .x4) (s.gpr .x5).toNat = result.2
  pub := PublicRegs [.x0, .x1, .x2, .x3, .x4, .x5, .x6]

end VG.Proof.Rc2.AArch64.Stream

end

/- Proofs formerly in `VerifiedGarbage.Proof.Rc2.AArch64.Stream.Copy`. -/
section

/-!
# Streaming RC2-CBC on AArch64: the byte copy

`copy src so dst dd cnt` (`Impl/Rc2/AArch64/Stream.lean`) writes the `cnt`
bytes at `src + so` to `dst + dd` (`writeBytes`), advancing `src` and `dst` by
the count; the one lemma (`copy_ok`) every call site uses.
-/

namespace VG.Proof.Rc2.AArch64.Stream

open VG VG.AArch64
open VG.Impl.Rc2.AArch64.Stream (copy copyBody)
open VG.Proof.MdStream.AArch64 (Upd Mupd wp_addImm wp_subImm wp_ldrb wp_strb eval_zero eval_nonzero
  ofNat_beq_zero sub_ofNat)
open VG.WriteBytes (writeBytes writeBytes_snoc writeBytes_frame writeBytes_nil)

theorem setWidth_byte (b : BitVec 8) : (b.setWidth 64).setWidth 8 = b := by
  ext i hi; simp

/-- The bytes just written. -/
theorem bytesAt_writeBytes (m : Mem) (q : Addr) (xs : List Byte) (h : xs.length ≤ 2 ^ 64) :
    Spec.Rc2.bytesAt (VG.WriteBytes.writeBytes m q xs) q xs.length = xs := by
  apply List.ext_getElem
  · simp [Spec.Rc2.bytesAt]
  · intro i h₁ h₂
    have hi : i < xs.length := h₂
    simp only [Spec.Rc2.bytesAt, List.getElem_map, List.getElem_range, VG.WriteBytes.writeBytes,
      Offset.add_sub_cancel_left, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le hi h), hi,
      ite_true, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]

/-- The copy's state after `j` of `k` bytes, from `s₀`. -/
structure CopyI (s₀ : State) (src dst cnt : Reg) (A B : Addr) (k j : Nat) (s : State) : Prop where
  j_le : j ≤ k
  psrc : s.gpr src = s₀.gpr src + BitVec.ofNat 64 j
  pdst : s.gpr dst = s₀.gpr dst + BitVec.ofNat 64 j
  pcnt : s.gpr cnt = BitVec.ofNat 64 (k - j)
  other : ∀ r, r ≠ .x9 → r ≠ src → r ≠ dst → r ≠ cnt → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  mem : s.mem = VG.WriteBytes.writeBytes s₀.mem B ((Spec.Rc2.bytesAt s₀.mem A k).take j)

/-- What the copy leaves. -/
structure CopyPost (s₀ : State) (src dst cnt : Reg) (A B : Addr) (k : Nat) (s : State) : Prop where
  psrc : s.gpr src = s₀.gpr src + BitVec.ofNat 64 k
  pdst : s.gpr dst = s₀.gpr dst + BitVec.ofNat 64 k
  other : ∀ r, r ≠ .x9 → r ≠ src → r ≠ dst → r ≠ cnt → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  mem : s.mem = VG.WriteBytes.writeBytes s₀.mem B (Spec.Rc2.bytesAt s₀.mem A k)

theorem CopyI.post {s₀ s : State} {src dst cnt : Reg} {A B : Addr} {k : Nat}
    (h : VG.Proof.Rc2.AArch64.Stream.CopyI s₀ src dst cnt A B k k s) : VG.Proof.Rc2.AArch64.Stream.CopyPost s₀ src dst cnt A B k s := by
  refine ⟨h.psrc, h.pdst, h.other, h.rd, h.wr, h.sp, ?_⟩
  rw [h.mem, List.take_of_length_le (by simp [Spec.Rc2.bytesAt])]

/-- The registers the copy uses are distinct. -/
structure Regs (src dst cnt : Reg) : Prop where
  sd : src ≠ dst
  sc : src ≠ cnt
  dc : dst ≠ cnt
  s9 : src ≠ .x9
  d9 : dst ≠ .x9
  c9 : cnt ≠ .x9

/-- Copying `k` bytes from `A = src + so` to `B = dst + dd`, when they may be
read and written and do not overlap. -/
theorem copy_ok {src dst cnt : Reg} {so dd : Nat} (hso : so < 4096) (hdd : dd < 4096)
    (hr : VG.Proof.Rc2.AArch64.Stream.Regs src dst cnt) {s₀ : State} {A B : Addr} {k : Nat}
    (hA : s₀.gpr src + BitVec.ofNat 64 so = A) (hB : s₀.gpr dst + BitVec.ofNat 64 dd = B)
    (hk : s₀.gpr cnt = BitVec.ofNat 64 k) (hk' : k < 2 ^ 64)
    (hsrc : ∀ i < k, InRegions (s₀.rd ++ s₀.wr) (A + BitVec.ofNat 64 i) 1)
    (hdst : ∀ i < k, InRegions s₀.wr (B + BitVec.ofNat 64 i) 1)
    (hd : Region.Disjoint ⟨A, k⟩ ⟨B, k⟩)
    {Q : State → Prop} (hQ : ∀ s, VG.Proof.Rc2.AArch64.Stream.CopyPost s₀ src dst cnt A B k s → Q s) :
    WP isa (copy src so dst dd cnt) s₀ Q := by
  have hI₀ : VG.Proof.Rc2.AArch64.Stream.CopyI s₀ src dst cnt A B k 0 s₀ :=
    ⟨Nat.zero_le _, by simp, by simp, by rw [hk, Nat.sub_zero], fun _ _ _ _ _ => rfl, rfl, rfl, rfl,
      by rw [List.take_zero, VG.WriteBytes.writeBytes_nil]⟩
  unfold copy
  refine WP.ite (decide (k = 0)) (by show VG.AArch64.eval (.zero .x cnt) s₀ = _; rw [VG.Proof.MdStream.AArch64.eval_zero, hk, ofNat_beq_zero hk'])
    (fun hb => WP.block_nil (hQ _ ?_)) (fun hb => ?_)
  · simp only [decide_eq_true_eq] at hb
    subst hb
    exact hI₀.post
  simp only [decide_eq_false_iff_not] at hb
  refine WP.loop (M := isa) (fun n (s : State) => ∃ j, n = k - j ∧ j < k ∧
      VG.Proof.Rc2.AArch64.Stream.CopyI s₀ src dst cnt A B k j s) ?_ k s₀ ⟨0, by omega, by omega, hI₀⟩
  rintro n s ⟨j, rfl, hj, h⟩
  -- The byte read.
  have hin : InRegions (s.rd ++ s.wr) (A + BitVec.ofNat 64 j) 1 := by
    rw [h.rd, h.wr]; exact hsrc j hj
  have hbyte : s.mem (A + BitVec.ofNat 64 j) = s₀.mem (A + BitVec.ofNat 64 j) := by
    rw [h.mem]
    exact (VG.WriteBytes.writeBytes_frame s₀.mem _ _ (R := ⟨B, k⟩)
      (by simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero, Nat.zero_add,
        List.length_take, Spec.Rc2.bytesAt, List.length_map, List.length_range]; omega)).bytes
      (R := ⟨A, k⟩) (by simpa using hd) (by show k ≤ 2 ^ 64; omega) hj
  have hout : InRegions s.wr (B + BitVec.ofNat 64 j) 1 := by
    rw [h.wr]; exact hdst j hj
  unfold copyBody
  refine wp_ldrb (a := A + BitVec.ofNat 64 j) hso ?_ hin fun s₁ u₁ => ?_
  · rw [h.psrc, ← hA, BitVec.add_assoc, BitVec.add_assoc, BitVec.add_comm (BitVec.ofNat 64 j)]
  refine wp_strb (a := B + BitVec.ofNat 64 j) hdd ?_ (by rw [u₁.wr]; exact hout) fun s₂ g₂ => ?_
  · rw [u₁.other _ hr.d9, h.pdst, ← hB, BitVec.add_assoc, BitVec.add_assoc,
      BitVec.add_comm (BitVec.ofNat 64 j)]
  refine wp_addImm (by decide) fun s₃ u₃ => wp_addImm (by decide) fun s₄ u₄ =>
    wp_subImm (by decide) fun s₅ u₅ => WP.block_nil ?_
  have hcnt : s₅.gpr cnt = BitVec.ofNat 64 (k - (j + 1)) := by
    rw [u₅.gpr, u₄.other _ hr.dc.symm, u₃.other _ hr.sc.symm, g₂.gpr, u₁.other _ hr.c9, h.pcnt,
      sub_ofNat (by omega), Nat.sub_sub]
  have hI : VG.Proof.Rc2.AArch64.Stream.CopyI s₀ src dst cnt A B k (j + 1) s₅ := by
    refine ⟨by omega, ?_, ?_, hcnt, fun x h1 h2 h3 h4 => ?_, ?_, ?_, ?_, ?_⟩
    · rw [u₅.other _ hr.sc, u₄.other _ hr.sd, u₃.gpr, g₂.gpr, u₁.other _ hr.s9, h.psrc,
        BitVec.add_assoc, ← BitVec.ofNat_add]
    · rw [u₅.other _ hr.dc, u₄.gpr, u₃.other _ hr.sd.symm, g₂.gpr, u₁.other _ hr.d9, h.pdst,
        BitVec.add_assoc, ← BitVec.ofNat_add]
    · rw [u₅.other x h4, u₄.other x h3, u₃.other x h2, g₂.gpr, u₁.other x h1, h.other x h1 h2 h3 h4]
    · rw [u₅.rd, u₄.rd, u₃.rd, g₂.rd, u₁.rd, h.rd]
    · rw [u₅.wr, u₄.wr, u₃.wr, g₂.wr, u₁.wr, h.wr]
    · rw [u₅.sp, u₄.sp, u₃.sp, g₂.sp, u₁.sp, h.sp]
    · have hj' : j < (Spec.Rc2.bytesAt s₀.mem A k).length := by simp [Spec.Rc2.bytesAt]; omega
      have hl : (List.take j (Spec.Rc2.bytesAt s₀.mem A k)).length = j := by
        rw [List.length_take, Nat.min_eq_left (Nat.le_of_lt hj')]
      rw [u₅.mem, u₄.mem, u₃.mem, g₂.mem, u₁.mem, u₁.gpr, hbyte, h.mem,
        List.take_add_one, List.getElem?_eq_getElem hj', Option.toList_some,
        VG.WriteBytes.writeBytes_snoc _ _ _ _ (by rw [hl]; omega), hl, VG.Proof.Rc2.AArch64.Stream.setWidth_byte]
      congr 1
      simp [Spec.Rc2.bytesAt]
  have hne : isa.eval (.nonzero .x cnt) s₅ = some (decide (k - (j + 1) ≠ 0)) := by
    show VG.AArch64.eval (.nonzero .x cnt) s₅ = _
    rw [VG.Proof.MdStream.AArch64.eval_nonzero, hcnt, bne, ofNat_beq_zero (by omega)]
    simp
  by_cases hjk : j + 1 = k
  · exact .inl ⟨by rw [hne]; simp; omega, hQ _ (hjk ▸ hI).post⟩
  · exact .inr ⟨by rw [hne]; simp; omega, k - (j + 1), by omega, j + 1, rfl, by omega, hI⟩

/-! ## The frame saving `x30` -/

theorem frame_push (s₀ : State) :
    Frame [⟨s₀.sp - 16, 16⟩] s₀.mem (s₀.mem.write (s₀.sp - 16) 8 (s₀.gpr .x30)) :=
  (Frame.refl _ _).write (List.mem_singleton_self _) _ (by simp [Region.Contains])

theorem fdepth_of_noFrames {c : Prog isa} (h : c.noFrames = true) : c.aarch64Depth = 0 := by
  induction c <;> simp_all [Code.noFrames, Code.aarch64Depth]

/-- The state the frame's body starts in. -/
def inner (s₀ : State) : State :=
  { s₀ with sp := s₀.sp - 16, mem := s₀.mem.write (s₀.sp - 16) 8 (s₀.gpr .x30) }

theorem inner_mem (s₀ : State) : (VG.Proof.Rc2.AArch64.Stream.inner s₀).mem = s₀.mem.write (s₀.sp - 16) 8 (s₀.gpr .x30) := rfl

end VG.Proof.Rc2.AArch64.Stream

end

/- Proofs formerly in `VerifiedGarbage.Proof.Rc2.AArch64.Stream.Prep`. -/
section

/-!
# Streaming RC2-CBC on AArch64: the copies before CBC

With complete blocks, the update copies the `p` pending bytes and the first
`out_len - p` bytes of data to `out`, and the rest of the data to `ctx + 136`,
then sets up the CBC call's arguments (`prep_ok`).
-/

namespace VG.Proof.Rc2.AArch64.Stream

open VG VG.AArch64
open VG.Impl.Rc2.AArch64.Stream (copy toOut toOutData toPending cbcArgs prep)
open VG.Proof.MdStream.AArch64 (Upd wp_mov wp_addImm wp_add wp_sub wp_lsr toNat_ofNat_lt sub_ofNat)
open VG.WriteBytes (writeBytes writeBytes_frame)

theorem ofNat_toNat' (x : BitVec 64) : x = BitVec.ofNat 64 x.toNat := by
  rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]

theorem inR {rs : List Region} {R : Region} {a : Addr} {n : Nat} (hR : R ∈ rs) (hc : R.Contains a n) :
    InRegions rs a n := ⟨R, hR, hc⟩

theorem shr3 {a : Nat} (h : a < 2 ^ 64) : BitVec.ofNat 64 a >>> 3 = BitVec.ofNat 64 (a / 8) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h,
    Nat.shiftRight_eq_div_pow, Nat.mod_eq_of_lt (by omega)]

/-- The arguments of an update, and their regions. -/
structure Lay (σ : State) (c dp op b : Addr) (p len ol : Nat) : Prop where
  x0 : σ.gpr .x0 = c
  x1 : σ.gpr .x1 = BitVec.ofNat 64 p
  x2 : σ.gpr .x2 = dp
  x3 : σ.gpr .x3 = BitVec.ofNat 64 len
  x4 : σ.gpr .x4 = op
  x5 : σ.gpr .x5 = BitVec.ofNat 64 ol
  x6 : σ.gpr .x6 = b
  rd : σ.rd = [⟨dp, len⟩]
  wr : σ.wr = [⟨c, 144⟩, ⟨op, ol⟩, ⟨b, 576⟩]
  cd : Region.Disjoint ⟨c, 144⟩ ⟨dp, len⟩
  co : Region.Disjoint ⟨c, 144⟩ ⟨op, ol⟩
  cb : Region.Disjoint ⟨c, 144⟩ ⟨b, 576⟩
  dout : Region.Disjoint ⟨dp, len⟩ ⟨op, ol⟩
  db : Region.Disjoint ⟨dp, len⟩ ⟨b, 576⟩
  ob : Region.Disjoint ⟨op, ol⟩ ⟨b, 576⟩
  fo : op.toNat + ol ≤ 2 ^ 64
  lenlt : len < 2 ^ 64
  ollt : ol < 2 ^ 64
  p8 : p < 8
  olq : ol = (p + len) / 8 * 8

/-- What the copies leave, for the CBC call. -/
structure CallSt (σ : State) (c dp op b : Addr) (p len ol : Nat) (s : State) : Prop where
  x0 : s.gpr .x0 = c
  x1 : s.gpr .x1 = c + BitVec.ofNat 64 128
  x2 : s.gpr .x2 = op
  x3 : s.gpr .x3 = BitVec.ofNat 64 ((p + len) / 8)
  x4 : s.gpr .x4 = b
  rd : s.rd = σ.rd
  wr : s.wr = σ.wr
  sp : s.sp = σ.sp
  out : Spec.Rc2.bytesAt s.mem op ol =
    Spec.Rc2.bytesAt σ.mem (c + BitVec.ofNat 64 136) p ++ Spec.Rc2.bytesAt σ.mem dp (ol - p)
  frame : Frame [⟨op, ol⟩, ⟨c + BitVec.ofNat 64 136, 8⟩] σ.mem s.mem
  pend : Spec.Rc2.bytesAt s.mem (c + BitVec.ofNat 64 136) (len + p - ol) =
    Spec.Rc2.bytesAt σ.mem (dp + BitVec.ofNat 64 (ol - p)) (len + p - ol)

theorem bytesAt_writeBytes' (m : Mem) (q src : Addr) (k : Nat) (hk : k ≤ 2 ^ 64) :
    Spec.Rc2.bytesAt (VG.WriteBytes.writeBytes m q (Spec.Rc2.bytesAt m src k)) q k = Spec.Rc2.bytesAt m src k := by
  have h := VG.Proof.Rc2.AArch64.Stream.bytesAt_writeBytes m q (Spec.Rc2.bytesAt m src k) (by rw [bytesAt_length]; exact hk)
  rwa [bytesAt_length] at h

theorem frame_writeBytes (m : Mem) (q src : Addr) (k : Nat) :
    Frame [⟨q, k⟩] m (VG.WriteBytes.writeBytes m q (Spec.Rc2.bytesAt m src k)) :=
  VG.WriteBytes.writeBytes_frame _ _ _ (by rw [bytesAt_length]; exact Region.contains_self _ _)

theorem prep_ok {σ : State} {c dp op b : Addr} {p len ol : Nat} (h : VG.Proof.Rc2.AArch64.Stream.Lay σ c dp op b p len ol)
    (hol : ol ≠ 0) :
    WP isa prep σ (VG.Proof.Rc2.AArch64.Stream.CallSt σ c dp op b p len ol) := by
  unfold prep
  have p8 := h.p8
  have olq := h.olq
  have fo := h.fo
  have hl := h.lenlt
  have hpo : p ≤ ol := by omega
  have hol8 : 8 ≤ ol := by omega
  have hrl : ol - p ≤ len := by omega
  have hr8 : len + p - ol < 8 := by omega
  have hc136 : ∀ i, i < 8 → InRegions σ.wr (c + BitVec.ofNat 64 136 + BitVec.ofNat 64 i) 1 := by
    intro i hi
    rw [h.wr, Offset.add_add]
    exact VG.Proof.Rc2.AArch64.Stream.inR (List.mem_cons_self ..) (Offset.contains_base _ (by omega) (by omega))
  have hctxSub : Region.Sub ⟨c + BitVec.ofNat 64 136, 8⟩ ⟨c, 144⟩ := Offset.sub_base _ (by omega)
  -- `toOut`, and the pending bytes to `out`.
  refine WP.seq (wp_mov fun s₁ u₁ => wp_mov fun s₂ u₂ => wp_mov fun s₃ u₃ => WP.block_nil ?_)
  have g₃ : ∀ r, r ≠ .x10 → r ≠ .x11 → r ≠ .x12 → s₃.gpr r = σ.gpr r := fun r h1 h2 h3 => by
    rw [u₃.other r h3, u₂.other r h2, u₁.other r h1]
  refine WP.seq (VG.Proof.Rc2.AArch64.Stream.copy_ok (A := c + BitVec.ofNat 64 136) (B := op) (k := p) (by decide) (by decide)
    ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩
    (by rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr, h.x0])
    (by rw [u₃.other _ (by decide), u₂.gpr, u₁.other _ (by decide), h.x4]; simp)
    (by rw [u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide), h.x1]) (by omega)
    (fun i hi => by
      rw [u₃.rd, u₃.wr, u₂.rd, u₂.wr, u₁.rd, u₁.wr]
      obtain ⟨R, hR, hc⟩ := hc136 i (by omega)
      exact ⟨R, List.mem_append_right _ hR, hc⟩)
    (fun i hi => by
      rw [u₃.wr, u₂.wr, u₁.wr, h.wr]
      exact VG.Proof.Rc2.AArch64.Stream.inR (R := ⟨op, ol⟩) (by simp) (Offset.contains_base _ (by omega) (by omega)))
    ((h.co.sub_left (Offset.sub_base _ (by omega))).sub_right (Region.sub_prefix hpo))
    fun s₄ c₄ => ?_)
  have m₄ : s₄.mem = VG.WriteBytes.writeBytes σ.mem op (Spec.Rc2.bytesAt σ.mem (c + BitVec.ofNat 64 136) p) := by
    rw [c₄.mem, u₃.mem, u₂.mem, u₁.mem]
  have g₄ : ∀ r, r ≠ .x9 → r ≠ .x10 → r ≠ .x11 → r ≠ .x12 → s₄.gpr r = σ.gpr r :=
    fun r h0 h1 h2 h3 => by rw [c₄.other r h0 h1 h2 h3, g₃ r h1 h2 h3]
  have x11₄ : s₄.gpr .x11 = op + BitVec.ofNat 64 p := by rw [c₄.pdst, u₃.other _ (by decide), u₂.gpr, u₁.other _ (by decide), h.x4]
  -- The first `ol - p` bytes of data after them.
  refine WP.seq (wp_sub fun s₅ u₅ => WP.block_nil ?_)
  have hd₄ : Spec.Rc2.bytesAt s₄.mem dp (ol - p) = Spec.Rc2.bytesAt σ.mem dp (ol - p) := by
    rw [m₄]
    exact Proof.Rc2.bytesAt_frame (VG.WriteBytes.writeBytes_frame _ _ _ (R := ⟨op, ol⟩) (by
      rw [bytesAt_length]; simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; omega))
      _ _ (by omega) (by simpa using (h.dout.sub_left (Region.sub_prefix hrl)))
  refine WP.seq (VG.Proof.Rc2.AArch64.Stream.copy_ok (A := dp) (B := op + BitVec.ofNat 64 p) (k := ol - p) (by decide) (by decide)
    ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩
    (by rw [u₅.other _ (by decide), g₄ _ (by decide) (by decide) (by decide) (by decide), h.x2]; simp)
    (by rw [u₅.other _ (by decide), x11₄]; simp)
    (by rw [u₅.gpr, g₄ _ (by decide) (by decide) (by decide) (by decide),
      g₄ _ (by decide) (by decide) (by decide) (by decide), h.x5, h.x1, sub_ofNat hpo]) (by omega)
    (fun i hi => by
      rw [u₅.rd, u₅.wr, c₄.rd, c₄.wr, u₃.rd, u₃.wr, u₂.rd, u₂.wr, u₁.rd, u₁.wr, h.rd]
      exact VG.Proof.Rc2.AArch64.Stream.inR (R := ⟨dp, len⟩) (by simp) (Offset.contains_base _ (by omega) (by omega)))
    (fun i hi => by
      rw [u₅.wr, c₄.wr, u₃.wr, u₂.wr, u₁.wr, h.wr, Offset.add_add]
      exact VG.Proof.Rc2.AArch64.Stream.inR (R := ⟨op, ol⟩) (by simp) (Offset.contains_base _ (by omega) (by omega)))
    ((h.dout.sub_left (Region.sub_prefix hrl)).sub_right (Offset.sub_base _ (by omega)))
    fun s₆ c₆ => ?_)
  have m₆ : s₆.mem = VG.WriteBytes.writeBytes s₄.mem (op + BitVec.ofNat 64 p) (Spec.Rc2.bytesAt s₄.mem dp (ol - p)) := by
    rw [c₆.mem, u₅.mem]
  have x2₆ : s₆.gpr .x2 = dp + BitVec.ofNat 64 (ol - p) := by
    rw [c₆.psrc, u₅.other _ (by decide), g₄ _ (by decide) (by decide) (by decide) (by decide), h.x2]
  have g₆ : ∀ r, r ≠ .x9 → r ≠ .x2 → r ≠ .x10 → r ≠ .x11 → r ≠ .x12 → s₆.gpr r = σ.gpr r :=
    fun r h0 h1 h2 h3 h4 => by rw [c₆.other r h0 h1 h3 h4, u₅.other r h4, g₄ r h0 h2 h3 h4]
  -- The rest of the data to `ctx + 136`.
  refine WP.seq (wp_add fun s₇ u₇ => wp_sub fun s₈ u₈ => wp_mov fun s₉ u₉ => WP.block_nil ?_)
  have hp₆ : Spec.Rc2.bytesAt s₆.mem (dp + BitVec.ofNat 64 (ol - p)) (len + p - ol) =
      Spec.Rc2.bytesAt σ.mem (dp + BitVec.ofNat 64 (ol - p)) (len + p - ol) := by
    have hs : Region.Sub ⟨dp + BitVec.ofNat 64 (ol - p), len + p - ol⟩ ⟨dp, len⟩ :=
      Offset.sub_base _ (by omega)
    rw [m₆, Proof.Rc2.bytesAt_frame (VG.Proof.Rc2.AArch64.Stream.frame_writeBytes _ _ _ _) _ _ (by omega)
      (by simpa using (h.dout.sub_left hs).sub_right (Offset.sub_base _ (by omega))), m₄,
      Proof.Rc2.bytesAt_frame (VG.Proof.Rc2.AArch64.Stream.frame_writeBytes _ _ _ _) _ _ (by omega)
      (by simpa using (h.dout.sub_left hs).sub_right (Region.sub_prefix hpo))]
  refine WP.seq (VG.Proof.Rc2.AArch64.Stream.copy_ok (A := dp + BitVec.ofNat 64 (ol - p)) (B := c + BitVec.ofNat 64 136)
    (k := len + p - ol) (by decide) (by decide)
    ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩
    (by rw [u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide), x2₆]; simp)
    (by rw [u₉.gpr, u₈.other _ (by decide), u₇.other _ (by decide),
      g₆ _ (by decide) (by decide) (by decide) (by decide) (by decide), h.x0])
    (by rw [u₉.other _ (by decide), u₈.gpr, u₇.gpr, u₇.other _ (by decide),
        g₆ _ (by decide) (by decide) (by decide) (by decide)
        (by decide), g₆ _ (by decide) (by decide) (by decide) (by decide) (by decide),
        g₆ _ (by decide) (by decide) (by decide) (by decide) (by decide), h.x3, h.x1, h.x5,
        BitVec.ofNat_add_ofNat, sub_ofNat (by omega)]) (by omega)
    (fun i hi => by
      rw [u₉.rd, u₉.wr, u₈.rd, u₈.wr, u₇.rd, u₇.wr, c₆.rd, c₆.wr, u₅.rd, u₅.wr, c₄.rd, c₄.wr, u₃.rd,
        u₃.wr, u₂.rd, u₂.wr, u₁.rd, u₁.wr, h.rd, Offset.add_add]
      exact VG.Proof.Rc2.AArch64.Stream.inR (R := ⟨dp, len⟩) (by simp) (Offset.contains_base _ (by omega) (by omega)))
    (fun i hi => by
      rw [u₉.wr, u₈.wr, u₇.wr, c₆.wr, u₅.wr, c₄.wr, u₃.wr, u₂.wr, u₁.wr]
      exact hc136 i (by omega))
    (((h.cd.sub_left hctxSub).sub_left (Region.sub_prefix (by omega))).sub_right
      (Offset.sub_base _ (by omega)) |>.symm)
    fun s₁₀ c₁₀ => ?_)
  have g₁₀ : ∀ r, r ≠ .x9 → r ≠ .x2 → r ≠ .x3 → r ≠ .x10 → r ≠ .x11 → r ≠ .x12 →
      s₁₀.gpr r = σ.gpr r := fun r h0 h1 h2 h3 h4 h5 => by
    rw [c₁₀.other r h0 h1 h3 h2, u₉.other r h3, u₈.other r h2, u₇.other r h2, g₆ r h0 h1 h3 h4 h5]
  -- The arguments of the CBC function.
  refine wp_addImm (by decide) fun s₁₁ u₁₁ => wp_mov fun s₁₂ u₁₂ => wp_lsr (by decide) fun s₁₃ u₁₃ =>
    wp_mov fun s₁₄ u₁₄ => WP.block_nil ?_
  have hm₁₀ : s₁₀.mem = VG.WriteBytes.writeBytes s₆.mem (c + BitVec.ofNat 64 136)
      (Spec.Rc2.bytesAt s₆.mem (dp + BitVec.ofNat 64 (ol - p)) (len + p - ol)) := by
    rw [c₁₀.mem, u₉.mem, u₈.mem, u₇.mem]
  have hm : s₁₄.mem = s₁₀.mem := by rw [u₁₄.mem, u₁₃.mem, u₁₂.mem, u₁₁.mem]
  -- The frames of the three copies.
  have f₄ : Frame [⟨op, ol⟩, ⟨c + BitVec.ofNat 64 136, 8⟩] σ.mem s₄.mem := by
    rw [m₄]; exact (VG.Proof.Rc2.AArch64.Stream.frame_writeBytes _ _ _ _).sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_cons_self .., Region.sub_prefix hpo⟩
  have f₆ : Frame [⟨op, ol⟩, ⟨c + BitVec.ofNat 64 136, 8⟩] s₄.mem s₆.mem := by
    rw [m₆]; exact (VG.Proof.Rc2.AArch64.Stream.frame_writeBytes _ _ _ _).sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_cons_self .., Offset.sub_base _ (by omega)⟩
  have f₁₀ : Frame [⟨op, ol⟩, ⟨c + BitVec.ofNat 64 136, 8⟩] s₆.mem s₁₀.mem := by
    rw [hm₁₀]; exact (VG.Proof.Rc2.AArch64.Stream.frame_writeBytes _ _ _ _).sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨⟨c + BitVec.ofNat 64 136, 8⟩, by simp, Region.sub_prefix (by omega)⟩
  have hoc : Region.Disjoint ⟨op, ol⟩ ⟨c + BitVec.ofNat 64 136, len + p - ol⟩ :=
    ((h.co.sub_left hctxSub).sub_left (Region.sub_prefix (by omega))).symm
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [u₁₄.other _ (by decide), u₁₃.other _ (by decide), u₁₂.other _ (by decide),
      u₁₁.other _ (by decide), g₁₀ _ (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide), h.x0]
  · rw [u₁₄.other _ (by decide), u₁₃.other _ (by decide), u₁₂.other _ (by decide), u₁₁.gpr,
      g₁₀ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h.x0]
  · rw [u₁₄.other _ (by decide), u₁₃.other _ (by decide), u₁₂.gpr,
      u₁₁.other _ (by decide), g₁₀ _ (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide), h.x4]
  · rw [u₁₄.other _ (by decide), u₁₃.gpr, u₁₂.other _ (by decide), u₁₁.other _ (by decide),
      g₁₀ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h.x5,
      VG.Proof.Rc2.AArch64.Stream.shr3 h.ollt, olq, Nat.mul_div_cancel _ (by decide)]
  · rw [u₁₄.gpr, u₁₃.other _ (by decide), u₁₂.other _ (by decide), u₁₁.other _ (by decide),
      g₁₀ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h.x6]
  · rw [u₁₄.rd, u₁₃.rd, u₁₂.rd, u₁₁.rd, c₁₀.rd, u₉.rd, u₈.rd, u₇.rd, c₆.rd, u₅.rd, c₄.rd, u₃.rd,
      u₂.rd, u₁.rd]
  · rw [u₁₄.wr, u₁₃.wr, u₁₂.wr, u₁₁.wr, c₁₀.wr, u₉.wr, u₈.wr, u₇.wr, c₆.wr, u₅.wr, c₄.wr, u₃.wr,
      u₂.wr, u₁.wr]
  · rw [u₁₄.sp, u₁₃.sp, u₁₂.sp, u₁₁.sp, c₁₀.sp, u₉.sp, u₈.sp, u₇.sp, c₆.sp, u₅.sp, c₄.sp, u₃.sp,
      u₂.sp, u₁.sp]
  · rw [hm, hm₁₀, Proof.Rc2.bytesAt_frame (VG.Proof.Rc2.AArch64.Stream.frame_writeBytes _ _ _ _) _ _ (by omega) (by simpa using hoc),
      show ol = p + (ol - p) by omega, bytesAt_add, Nat.add_sub_cancel_left, m₆,
      Proof.Rc2.bytesAt_frame (VG.Proof.Rc2.AArch64.Stream.frame_writeBytes _ _ _ _) _ _ (by omega)
        (by simpa using Offset.base_disjoint op (Nat.le_refl p) (by omega)),
      VG.Proof.Rc2.AArch64.Stream.bytesAt_writeBytes' _ _ _ _ (by omega), hd₄, m₄, VG.Proof.Rc2.AArch64.Stream.bytesAt_writeBytes' _ _ _ _ (by omega)]
  · rw [hm]; exact f₄.trans (f₆.trans f₁₀)
  · rw [hm, hm₁₀, VG.Proof.Rc2.AArch64.Stream.bytesAt_writeBytes' _ _ _ _ (by omega), hp₆]

end VG.Proof.Rc2.AArch64.Stream

end

/- Proofs formerly in `VerifiedGarbage.Proof.Rc2.AArch64.Stream.Init`. -/
section

/-!
# Streaming RC2-CBC on AArch64: `init`

The length checks, each a subtraction and a shift tested with `cbnz` (`chk`),
return 1, 2 or 3 (`init_post_error`); otherwise, inside the frame saving
`x30`, the IV is copied to `ctx + 128` and the verified key expansion writes
the schedule to `ctx` (`main_ok`, `init_post`).
-/

namespace VG.Proof.Rc2.AArch64.Stream

open VG VG.AArch64
open VG.Impl.Rc2.AArch64.Stream (init initMain initArgs keyCall checkKey checkBits checkIv)
open VG.Proof.MdStream.AArch64 (Upd Mupd wp_mov wp_movz wp_subImm wp_lsr wp_ldr wp_str toNat_ofNat_lt
  eval_nonzero sub_beq)

/-- `(x - 1) >> sh` is nonzero unless `x` is in `1..=2^sh`. -/
theorem chk (x : BitVec 64) {sh p : Nat} (hs : sh < 64) (hp : 2 ^ sh = p) :
    ((x - BitVec.ofNat 64 1) >>> sh != 0) = decide ¬(1 ≤ x.toNat ∧ x.toNat ≤ p) := by
  have hx := x.isLt
  have hp' : p ≤ 2 ^ 63 := hp ▸ Nat.pow_le_pow_right (by decide) (by omega)
  have hp0 : 0 < p := hp ▸ Nat.two_pow_pos sh
  have e : ((x - BitVec.ofNat 64 1) >>> sh).toNat = (2 ^ 64 - 1 + x.toNat) % 2 ^ 64 / p := by
    rw [BitVec.toNat_ushiftRight, BitVec.toNat_sub, Nat.shiftRight_eq_div_pow, hp]
    rfl
  have z : (0 : BitVec 64).toNat = 0 := rfl
  rw [Bool.eq_iff_iff, bne_iff_ne, ne_eq, decide_eq_true_eq, ← BitVec.toNat_inj, e, z,
    Nat.div_eq_zero_iff]
  by_cases h0 : x.toNat = 0
  · rw [h0]; omega
  · rw [show (2 ^ 64 - 1 + x.toNat) % 2 ^ 64 = x.toNat - 1 by omega]; omega

/-- The arguments of `init`, and their regions, for valid lengths. -/
structure ILay (σ : State) (key iv ctx scr : Addr) (kl eb : Nat) : Prop where
  x0 : σ.gpr .x0 = key
  x1 : σ.gpr .x1 = BitVec.ofNat 64 kl
  x2 : σ.gpr .x2 = BitVec.ofNat 64 eb
  x3 : σ.gpr .x3 = iv
  x5 : σ.gpr .x5 = ctx
  x6 : σ.gpr .x6 = scr
  rd : σ.rd = [⟨key, kl⟩, ⟨iv, 8⟩]
  wr : σ.wr = [⟨ctx, 144⟩, ⟨scr, 576⟩]
  kc : Region.Disjoint ⟨key, kl⟩ ⟨ctx, 144⟩
  ks : Region.Disjoint ⟨key, kl⟩ ⟨scr, 576⟩
  ic : Region.Disjoint ⟨iv, 8⟩ ⟨ctx, 144⟩
  cs : Region.Disjoint ⟨ctx, 144⟩ ⟨scr, 576⟩
  hk : 1 ≤ kl ∧ kl ≤ 128
  he : 1 ≤ eb ∧ eb ≤ 1024

theorem expandKey_noFrames : Impl.Rc2.AArch64.expandKey.noFrames = true := by lit_decide

/-- The IV, the key expansion and 0, without the frame. -/
theorem main_ok {σ : State} {key iv ctx scr : Addr} {kl eb : Nat} (h : VG.Proof.Rc2.AArch64.Stream.ILay σ key iv ctx scr kl eb) :
    WP isa initMain σ fun s' => (∀ r ∈ preserved, r ≠ .x30 → s'.gpr r = σ.gpr r) ∧
      BitVec.setWidth 32 (s'.gpr .x0) = 0 ∧
      Spec.Rc2.scheduleAt s'.mem ctx = Spec.Rc2.expandKey (Spec.Rc2.bytesAt σ.mem key kl) eb ∧
      Spec.Rc2.blockAt s'.mem (ctx + 128) = Spec.Rc2.blockAt σ.mem iv := by
  have hk := h.hk
  have he := h.he
  have ivS : Region.Sub ⟨ctx + BitVec.ofNat 64 128, 8⟩ ⟨ctx, 144⟩ := Offset.sub_base _ (by omega)
  have schS : Region.Sub ⟨ctx, 128⟩ ⟨ctx, 144⟩ := Region.sub_prefix (by omega)
  have bufS : Region.Sub ⟨scr, 512⟩ ⟨scr, 576⟩ := Region.sub_prefix (by omega)
  unfold initMain initArgs
  refine WP.seq (wp_ldr (a := iv) ⟨by decide, by decide⟩ (by rw [h.x3]; simp)
    (by rw [h.rd]; exact VG.Proof.Rc2.AArch64.Stream.inR (R := ⟨iv, 8⟩) (by simp) (Region.contains_self _ _)) fun s₁ u₁ => ?_)
  refine wp_str (a := ctx + BitVec.ofNat 64 128) ⟨by decide, by decide⟩
    (by rw [u₁.other _ (by decide), h.x5])
    (by rw [u₁.wr, h.wr]; exact VG.Proof.Rc2.AArch64.Stream.inR (R := ⟨ctx, 144⟩) (by simp) (Offset.contains_base _ (by omega) (by omega)))
    fun s₂ g₂ => wp_mov fun s₃ u₃ => wp_mov fun s₄ u₄ => WP.block_nil ?_
  have g₄ : ∀ r, r ≠ .x3 → r ≠ .x4 → r ≠ .x8 → s₄.gpr r = σ.gpr r := fun r h3 h4 h8 => by
    rw [u₄.other r h4, u₃.other r h3, g₂.gpr, u₁.other r h8]
  have m₄ : s₄.mem = σ.mem.writeW (ctx + BitVec.ofNat 64 128) (σ.mem.readW iv 64) := by
    rw [u₄.mem, u₃.mem, g₂.mem, u₁.gpr, u₁.mem]
  have e0 : s₄.callEntry.gpr .x0 = key :=
    (State.callEntry_gpr _ (by decide)).trans ((g₄ _ (by decide) (by decide) (by decide)).trans h.x0)
  have e1 : s₄.callEntry.gpr .x1 = BitVec.ofNat 64 kl :=
    (State.callEntry_gpr _ (by decide)).trans ((g₄ _ (by decide) (by decide) (by decide)).trans h.x1)
  have e2 : s₄.callEntry.gpr .x2 = BitVec.ofNat 64 eb :=
    (State.callEntry_gpr _ (by decide)).trans ((g₄ _ (by decide) (by decide) (by decide)).trans h.x2)
  have e3 : s₄.callEntry.gpr .x3 = ctx := (State.callEntry_gpr _ (by decide)).trans (by
    rw [u₄.other _ (by decide), u₃.gpr, g₂.gpr, u₁.other _ (by decide), h.x5])
  have e4 : s₄.callEntry.gpr .x4 = scr := (State.callEntry_gpr _ (by decide)).trans (by
    rw [u₄.gpr, u₃.other _ (by decide), g₂.gpr, u₁.other _ (by decide), h.x6])
  have hkl : (BitVec.ofNat 64 kl).toNat = kl := toNat_ofNat_lt (by omega)
  have heb : (BitVec.ofNat 64 eb).toNat = eb := toNat_ofNat_lt (by omega)
  have zero : ∀ x : Addr, x = x + BitVec.ofNat 64 0 := fun x => by simp
  have rd₄ : s₄.rd = σ.rd := by rw [u₄.rd, u₃.rd, g₂.rd, u₁.rd]
  have wr₄ : s₄.wr = σ.wr := by rw [u₄.wr, u₃.wr, g₂.wr, u₁.wr]
  refine WP.seq (WP.call (k := keyContract) key_correct (rd := [⟨key, kl⟩])
    (wr := [⟨ctx, 128⟩, ⟨scr, 512⟩]) ?_ ?_ ?_ ?_ VG.Proof.Rc2.AArch64.Stream.expandKey_noFrames)
  · simp only [keyContract, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr, e0, e1, e2,
      e3, e4, hkl, heb]
    exact ⟨trivial, trivial, h.kc.sub_right schS, h.ks.sub_right bufS,
      (h.cs.sub_left schS).sub_right bufS, hk.1, hk.2, he.1, he.2⟩
  · rw [rd₄, wr₄, h.rd, h.wr]
    refine Covers.of_sub fun r hr => ?_
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨⟨key, kl⟩, by simp, 0, zero key, by dsimp only; omega⟩
    · exact ⟨⟨ctx, 144⟩, by simp, 0, zero ctx, by dsimp only; omega⟩
    · exact ⟨⟨scr, 576⟩, by simp, 0, zero scr, by dsimp only; omega⟩
  · rw [wr₄, h.wr]
    refine Covers.of_sub fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨⟨ctx, 144⟩, by simp, 0, zero ctx, by dsimp only; omega⟩
    · exact ⟨⟨scr, 576⟩, by simp, 0, zero scr, by dsimp only; omega⟩
  intro s' hr hw hsp hf hcs _ hpost
  simp only [keyContract, State.withRegions_gpr, State.withRegions_mem, State.callEntry_mem, e0, e1, e2,
    e3, hkl, heb] at hpost
  refine wp_movz fun s₅ u₅ => WP.block_nil ⟨fun r hr h30 => ?_, by rw [u₅.gpr]; rfl, ?_, ?_⟩
  · have hne : ∀ r ∈ preserved, r ≠ .x0 ∧ r ≠ .x3 ∧ r ≠ .x4 ∧ r ≠ .x8 := by decide
    obtain ⟨h0, h3, h4, h8⟩ := hne r hr
    rw [u₅.other r h0, hcs r hr h30, g₄ r h3 h4 h8]
  · rw [u₅.mem, hpost, m₄, Proof.Rc2.bytesAt_frame (frame_store64 _ _ _) _ _ (by omega)
      (by simpa using h.kc.sub_right ivS)]
  · rw [u₅.mem, blockAt_frame hf (ctx + 128) (by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro r (rfl | rfl)
      · exact Offset.disjoint_base ctx (k := 128) (d := 128) (n := 8) (by omega) (by omega)
      · exact (h.cs.sub_left ivS).sub_right bufS), m₄]
    exact blockAt_copy _ _ _

theorem init_correct (s₀ : State) (hs : initContract.pre s₀) :
    WP isa init s₀ fun s' => GprAbi s₀ s' ∧ initContract.post s₀ s' := by
  obtain ⟨sp16, hrd, hwr, kc, ks, ic, is, cs, sk, si, sc, ss, -, -⟩ := hs
  have np : ∀ r ∈ preserved, r ≠ .x0 ∧ r ≠ .x8 := by decide
  unfold init checkKey
  refine WP.seq (wp_subImm (by decide) fun s₁ u₁ => wp_lsr (by decide) fun s₂ u₂ => WP.block_nil ?_)
  refine WP.ite (decide ¬(1 ≤ (s₀.gpr .x1).toNat ∧ (s₀.gpr .x1).toNat ≤ 128))
    (by show VG.AArch64.eval (.nonzero .x .x8) s₂ = _
        rw [VG.Proof.MdStream.AArch64.eval_nonzero, u₂.gpr, u₁.gpr, VG.Proof.Rc2.AArch64.Stream.chk _ (p := 128) (by decide) (by decide)]) (fun hb => ?_) (fun hb => ?_)
  · simp only [decide_eq_true_eq] at hb
    refine wp_movz fun s₃ u₃ => WP.block_nil ⟨⟨fun r hr => ?_, by rw [u₃.sp, u₂.sp, u₁.sp]⟩, ?_⟩
    · rw [u₃.other r (np r hr).1, u₂.other r (np r hr).2, u₁.other r (np r hr).2]
    · exact Proof.Rc2.init_post_error (by rw [u₃.gpr]; simp only [hb, not_false_eq_true, ite_true]; rfl) fun h => hb h.1
  simp only [decide_eq_false_iff_not, Decidable.not_not] at hb
  have g₂ : ∀ r, r ≠ .x8 → s₂.gpr r = s₀.gpr r := fun r h => by rw [u₂.other r h, u₁.other r h]
  unfold checkBits
  refine WP.seq (wp_subImm (by decide) fun s₃ u₃ => wp_lsr (by decide) fun s₄ u₄ => WP.block_nil ?_)
  refine WP.ite (decide ¬(1 ≤ (s₀.gpr .x2).toNat ∧ (s₀.gpr .x2).toNat ≤ 1024))
    (by show VG.AArch64.eval (.nonzero .x .x8) s₄ = _
        rw [VG.Proof.MdStream.AArch64.eval_nonzero, u₄.gpr, u₃.gpr, g₂ _ (by decide), VG.Proof.Rc2.AArch64.Stream.chk _ (p := 1024) (by decide) (by decide)])
    (fun hb' => ?_) (fun hb' => ?_)
  · simp only [decide_eq_true_eq] at hb'
    refine wp_movz fun s₅ u₅ => WP.block_nil ⟨⟨fun r hr => ?_, by rw [u₅.sp, u₄.sp, u₃.sp, u₂.sp, u₁.sp]⟩, ?_⟩
    · rw [u₅.other r (np r hr).1, u₄.other r (np r hr).2, u₃.other r (np r hr).2, g₂ r (np r hr).2]
    · exact Proof.Rc2.init_post_error (by rw [u₅.gpr]; simp only [hb, hb', and_self, not_true_eq_false, not_false_eq_true, ite_true, ite_false]; rfl)
        fun h => hb' h.2.1
  simp only [decide_eq_false_iff_not, Decidable.not_not] at hb'
  have g₄ : ∀ r, r ≠ .x8 → s₄.gpr r = s₀.gpr r := fun r h => by rw [u₄.other r h, u₃.other r h, g₂ r h]
  unfold checkIv
  refine WP.seq (wp_subImm (by decide) fun s₅ u₅ => WP.block_nil ?_)
  have eiv := sub_beq (a := (s₀.gpr .x4).toNat) (b := 8) (s₀.gpr .x4).isLt (by decide)
  rw [← VG.Proof.Rc2.AArch64.Stream.ofNat_toNat' (s₀.gpr .x4)] at eiv
  refine WP.ite (!decide ((s₀.gpr .x4).toNat = 8))
    (by show VG.AArch64.eval (.nonzero .x .x8) s₅ = _
        rw [VG.Proof.MdStream.AArch64.eval_nonzero, u₅.gpr, g₄ _ (by decide), bne, eiv]) (fun hb'' => ?_) (fun hb'' => ?_)
  · simp only [Bool.not_eq_true', decide_eq_false_iff_not] at hb''
    refine wp_movz fun s₆ u₆ => WP.block_nil ⟨⟨fun r hr => ?_, by
      rw [u₆.sp, u₅.sp, u₄.sp, u₃.sp, u₂.sp, u₁.sp]⟩, ?_⟩
    · rw [u₆.other r (np r hr).1, u₅.other r (np r hr).2, g₄ r (np r hr).2]
    · exact Proof.Rc2.init_post_error
        (by rw [u₆.gpr]; simp only [hb, hb', and_self, not_true_eq_false, ite_false]; rfl)
        fun h => hb'' h.2.2
  simp only [Bool.not_eq_false', decide_eq_true_eq] at hb''
  have g₅ : ∀ r, r ≠ .x8 → s₅.gpr r = s₀.gpr r := fun r h => by rw [u₅.other r h, g₄ r h]
  have hσ : VG.Proof.Rc2.AArch64.Stream.ILay (VG.Proof.Rc2.AArch64.Stream.inner s₅) (s₀.gpr .x0) (s₀.gpr .x3) (s₀.gpr .x5) (s₀.gpr .x6) (s₀.gpr .x1).toNat
      (s₀.gpr .x2).toNat := by
    have r₅ : s₅.rd = s₀.rd := by rw [u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd]
    have w₅ : s₅.wr = s₀.wr := by rw [u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]
    refine ⟨g₅ _ (by decide), (g₅ _ (by decide)).trans (VG.Proof.Rc2.AArch64.Stream.ofNat_toNat' _),
      (g₅ _ (by decide)).trans (VG.Proof.Rc2.AArch64.Stream.ofNat_toNat' _), g₅ _ (by decide), g₅ _ (by decide), g₅ _ (by decide),
      ?_, w₅.trans hwr, kc, ks, ?_, cs, hb, hb'⟩
    · show s₅.rd = _; rw [r₅, hrd, hb'']
    · rw [← hb'']; exact ic
  have sp₅ : s₅.sp = s₀.sp := by rw [u₅.sp, u₄.sp, u₃.sp, u₂.sp, u₁.sp]
  have mem₅ : s₅.mem = s₀.mem := by rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  refine WP.frameReg (by rw [sp₅]; exact sp16) (fun R hR => ?_)
    (WP.mono (VG.Proof.Rc2.AArch64.Stream.main_ok hσ) fun s₂ ⟨hk, hr, hs, hiv⟩ => ?_)
    (by rw [VG.Proof.Rc2.AArch64.Stream.fdepth_of_noFrames (by lit_decide : initMain.noFrames = true)]; decide)
  · rw [u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr, hwr] at hR
    rw [sp₅]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hR
    rcases hR with rfl | rfl
    · exact sc
    · exact ss
  refine ⟨⟨fun r hr => ?_, sp₅⟩, ?_⟩
  · by_cases h30 : r = .x30
    · subst h30; simp [State.write, g₅ .x30 (by decide)]
    · simp only [State.write, h30, ite_false]
      exact (hk r hr h30).trans (g₅ r (np r hr).2)
  · have hf := VG.Proof.Rc2.AArch64.Stream.frame_push s₅
    rw [mem₅, sp₅, g₅ .x30 (by decide)] at hf
    have e₁ : Spec.Rc2.bytesAt (VG.Proof.Rc2.AArch64.Stream.inner s₅).mem (s₀.gpr .x0) (s₀.gpr .x1).toNat =
        Spec.Rc2.bytesAt s₀.mem (s₀.gpr .x0) (s₀.gpr .x1).toNat := by
      rw [VG.Proof.Rc2.AArch64.Stream.inner_mem, mem₅, sp₅, g₅ .x30 (by decide)]
      exact Proof.Rc2.bytesAt_frame hf _ _ (by omega) (by simpa using sk.symm)
    have e₂ : Spec.Rc2.blockAt (VG.Proof.Rc2.AArch64.Stream.inner s₅).mem (s₀.gpr .x3) = Spec.Rc2.blockAt s₀.mem (s₀.gpr .x3) := by
      rw [VG.Proof.Rc2.AArch64.Stream.inner_mem, mem₅, sp₅, g₅ .x30 (by decide)]
      exact blockAt_frame hf _ (by rw [hb''] at si; simpa using si.symm)
    have hs' : Spec.Rc2.scheduleAt s₂.mem (s₀.gpr .x5) =
        Spec.Rc2.expandKey (Spec.Rc2.bytesAt (VG.Proof.Rc2.AArch64.Stream.inner s₅).mem (s₀.gpr .x0) (s₀.gpr .x1).toNat)
          (s₀.gpr .x2).toNat := hs
    have hiv' : Spec.Rc2.blockAt s₂.mem (s₀.gpr .x5 + 128) =
        Spec.Rc2.blockAt (VG.Proof.Rc2.AArch64.Stream.inner s₅).mem (s₀.gpr .x3) := hiv
    rw [e₁] at hs'
    rw [e₂] at hiv'
    exact Proof.Rc2.init_post hb hb' hb'' hr hs' hiv'

end VG.Proof.Rc2.AArch64.Stream

end

/- Proofs formerly in `VerifiedGarbage.Proof.Rc2.AArch64.Stream.Update`. -/
section

/-!
# Streaming RC2-CBC on AArch64: the update functions

With no complete block, the data is appended to the pending bytes
(`short_ok`); otherwise, inside the frame saving `x30`, the copies (`prep_ok`)
are followed by the call of the verified CBC function (`call_ok`).
`update_post_short` and `update_post_long` (`Proof/Rc2/Stream.lean`) turn the
memory each leaves into the contract's postcondition.
-/

namespace VG.Proof.Rc2.AArch64.Stream

open VG VG.AArch64
open VG.Impl.Rc2.AArch64.Stream (copy short prep longMain cbcCall update)
open VG.Proof.MdStream.AArch64 (Upd wp_add toNat_ofNat_lt eval_zero ofNat_beq_zero)
open VG.WriteBytes (writeBytes)

/-! ## The CBC call -/

theorem cbc_correct' (d : Spec.Rc2.Direction) (s : State) (hs : (Cbc.contract d).pre s) :
    ∃ t s', Exec isa (Impl.Rc2.AArch64.Cbc.code d) s t s' ∧ abiPreserved s s' ∧
      (Cbc.contract d).post s s' := by
  cases d
  · exact Cbc.encrypt_correct s hs
  · exact Cbc.decrypt_correct s hs

theorem cbcCall_eq (d : Spec.Rc2.Direction) : cbcCall d =
    .call (match d with | .encrypt => "vg_rc2_cbc_encrypt" | .decrypt => "vg_rc2_cbc_decrypt")
      (Impl.Rc2.AArch64.Cbc.code d) := by cases d <;> rfl

theorem cbc_noFrames (d : Spec.Rc2.Direction) : (Impl.Rc2.AArch64.Cbc.code d).noFrames = true := by
  cases d
  · change Impl.Rc2.AArch64.Cbc.encrypt.noFrames = true; lit_decide
  · change Impl.Rc2.AArch64.Cbc.decrypt.noFrames = true; lit_decide

/-- The CBC function on the `n` blocks at `op`, with the schedule at `c` and the
chaining value at `c + 128`, with the update's regions. -/
theorem call_ok (d : Spec.Rc2.Direction) {s : State} {c dp op b : Addr} {len ol n : Nat}
    (h0 : s.gpr .x0 = c) (h1 : s.gpr .x1 = c + BitVec.ofNat 64 128) (h2 : s.gpr .x2 = op)
    (h3 : s.gpr .x3 = BitVec.ofNat 64 n) (h4 : s.gpr .x4 = b) (hn : 8 * n = ol) (hol : ol < 2 ^ 64)
    (hrd : s.rd = [⟨dp, len⟩]) (hwr : s.wr = [⟨c, 144⟩, ⟨op, ol⟩, ⟨b, 576⟩])
    (co : Region.Disjoint ⟨c, 144⟩ ⟨op, ol⟩) (cb : Region.Disjoint ⟨c, 144⟩ ⟨b, 576⟩)
    (ob : Region.Disjoint ⟨op, ol⟩ ⟨b, 576⟩) (fo : op.toNat + ol ≤ 2 ^ 64)
    {Q : State → Prop}
    (hQ : ∀ s', s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp →
      Frame [⟨c + BitVec.ofNat 64 128, 8⟩, ⟨op, 8 * n⟩, ⟨b, 512⟩] s.mem s'.mem →
      (∀ r ∈ preserved, r ≠ .x30 → s'.gpr r = s.gpr r) →
      Spec.Rc2.blocksAt s'.mem op n = (Spec.Rc2.cbc (Spec.Rc2.scheduleAt s.mem c) d
        (Spec.Rc2.blockAt s.mem (c + BitVec.ofNat 64 128)) (Spec.Rc2.blocksAt s.mem op n)).1 →
      Spec.Rc2.blockAt s'.mem (c + BitVec.ofNat 64 128) = (Spec.Rc2.cbc (Spec.Rc2.scheduleAt s.mem c) d
        (Spec.Rc2.blockAt s.mem (c + BitVec.ofNat 64 128)) (Spec.Rc2.blocksAt s.mem op n)).2 →
      Q s') :
    WP isa (cbcCall d) s Q := by
  have e0 : s.callEntry.gpr .x0 = c := (State.callEntry_gpr _ (by decide)).trans h0
  have e1 : s.callEntry.gpr .x1 = c + BitVec.ofNat 64 128 := (State.callEntry_gpr _ (by decide)).trans h1
  have e2 : s.callEntry.gpr .x2 = op := (State.callEntry_gpr _ (by decide)).trans h2
  have e3 : s.callEntry.gpr .x3 = BitVec.ofNat 64 n := (State.callEntry_gpr _ (by decide)).trans h3
  have e4 : s.callEntry.gpr .x4 = b := (State.callEntry_gpr _ (by decide)).trans h4
  have hn' : (BitVec.ofNat 64 n).toNat = n := toNat_ofNat_lt (by omega)
  have ivS : Region.Sub ⟨c + BitVec.ofNat 64 128, 8⟩ ⟨c, 144⟩ := Offset.sub_base _ (by omega)
  have keyS : Region.Sub ⟨c, 128⟩ ⟨c, 144⟩ := Region.sub_prefix (by omega)
  have outS : Region.Sub ⟨op, 8 * n⟩ ⟨op, ol⟩ := Region.sub_prefix (by omega)
  have bufS : Region.Sub ⟨b, 512⟩ ⟨b, 576⟩ := Region.sub_prefix (by omega)
  have zero : ∀ x : Addr, x = x + BitVec.ofNat 64 0 := fun x => by simp
  rw [VG.Proof.Rc2.AArch64.Stream.cbcCall_eq]
  refine WP.call (k := Cbc.contract d) (VG.Proof.Rc2.AArch64.Stream.cbc_correct' d) (rd := [⟨c, 128⟩])
    (wr := [⟨c + BitVec.ofNat 64 128, 8⟩, ⟨op, 8 * n⟩, ⟨b, 512⟩]) ?_ ?_ ?_ ?_ (VG.Proof.Rc2.AArch64.Stream.cbc_noFrames d)
  · simp only [Cbc.contract, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr, e0, e1, e2,
      e3, e4, hn']
    exact ⟨trivial, trivial, Offset.base_disjoint _ (Nat.le_refl _) (by omega),
      (co.sub_left keyS).sub_right outS, (cb.sub_left keyS).sub_right bufS,
      (co.sub_left ivS).sub_right outS, (cb.sub_left ivS).sub_right bufS,
      (ob.sub_left outS).sub_right bufS, by omega⟩
  · rw [hrd, hwr]
    refine Covers.of_sub fun r hr => ?_
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨⟨c, 144⟩, by simp, 0, zero c, by dsimp only; omega⟩
    · exact ⟨⟨c, 144⟩, by simp, 128, rfl, by dsimp only; omega⟩
    · exact ⟨⟨op, ol⟩, by simp, 0, zero op, by dsimp only; omega⟩
    · exact ⟨⟨b, 576⟩, by simp, 0, zero b, by dsimp only; omega⟩
  · rw [hwr]
    refine Covers.of_sub fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨⟨c, 144⟩, by simp, 128, rfl, by dsimp only; omega⟩
    · exact ⟨⟨op, ol⟩, by simp, 0, zero op, by dsimp only; omega⟩
    · exact ⟨⟨b, 576⟩, by simp, 0, zero b, by dsimp only; omega⟩
  · intro s' hr hw hsp hf hcs _ hpost
    simp only [Cbc.contract, State.withRegions_gpr, State.withRegions_mem, State.callEntry_mem, e0, e1, e2,
      e3, hn'] at hpost
    exact hQ s' hr hw hsp hf hcs hpost.1 hpost.2

/-! ## The postcondition -/

/-- The update's postcondition, for the arguments of `Lay`. -/
def UPost (d : Spec.Rc2.Direction) (σ : State) (c dp op : Addr) (p len ol : Nat) (s' : State) : Prop :=
  Spec.Rc2.contextAt s'.mem c d ((p + len) % 8) =
      (Spec.Rc2.update (Spec.Rc2.contextAt σ.mem c d p) (Spec.Rc2.bytesAt σ.mem dp len)).1 ∧
    Spec.Rc2.bytesAt s'.mem op ol =
      (Spec.Rc2.update (Spec.Rc2.contextAt σ.mem c d p) (Spec.Rc2.bytesAt σ.mem dp len)).2

/-! ## No complete block -/

theorem short_ok (d : Spec.Rc2.Direction) {σ : State} {c dp op b : Addr} {p len ol : Nat}
    (h : VG.Proof.Rc2.AArch64.Stream.Lay σ c dp op b p len ol) (hol : ol = 0) :
    WP isa short σ fun s' => (∀ r ∈ preserved, s'.gpr r = σ.gpr r) ∧ s'.sp = σ.sp ∧
      VG.Proof.Rc2.AArch64.Stream.UPost d σ c dp op p len ol s' := by
  have p8 := h.p8
  have olq := h.olq
  have hpl : p + len < 8 := by omega
  unfold short
  refine WP.seq (wp_add fun s₁ u₁ => WP.block_nil ?_)
  refine VG.Proof.Rc2.AArch64.Stream.copy_ok (A := dp) (B := c + BitVec.ofNat 64 (136 + p)) (k := len) (by decide) (by decide)
    ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩
    (by rw [u₁.other _ (by decide), h.x2]; simp)
    (by rw [u₁.gpr, h.x0, h.x1, Offset.add_add, Nat.add_comm])
    (by rw [u₁.other _ (by decide), h.x3]) h.lenlt
    (fun i hi => by
      rw [u₁.rd, u₁.wr, h.rd]
      exact VG.Proof.Rc2.AArch64.Stream.inR (R := ⟨dp, len⟩) (by simp) (Offset.contains_base _ (by omega) (by omega)))
    (fun i hi => by
      rw [u₁.wr, h.wr, Offset.add_add]
      exact VG.Proof.Rc2.AArch64.Stream.inR (R := ⟨c, 144⟩) (by simp) (Offset.contains_base _ (by omega) (by omega)))
    (h.cd.sub_left (Offset.sub_base _ (by omega))).symm fun s' cp => ?_
  have hm : s'.mem = VG.WriteBytes.writeBytes σ.mem (c + BitVec.ofNat 64 (136 + p)) (Spec.Rc2.bytesAt σ.mem dp len) := by
    rw [cp.mem, u₁.mem]
  have hf := VG.Proof.Rc2.AArch64.Stream.frame_writeBytes σ.mem (c + BitVec.ofNat 64 (136 + p)) dp len
  rw [← hm] at hf
  refine ⟨fun r hr => ?_, by rw [cp.sp, u₁.sp], ?_⟩
  · have hne : ∀ r ∈ preserved, r ≠ .x9 ∧ r ≠ .x2 ∧ r ≠ .x8 ∧ r ≠ .x3 := by decide
    obtain ⟨h1, h2, h3, h4⟩ := hne r hr
    rw [cp.other r h1 h2 h3 h4, u₁.other r h3]
  obtain ⟨r1, r2⟩ := update_post_short (d := d) (out := op) hpl
    (scheduleAt_frame hf c (by simpa using Offset.base_disjoint c (by omega) (by omega)))
    (blockAt_frame hf (c + 128) (by simpa using Offset.disjoint c (d := 128) (by omega) (by omega) (by omega)))
    (by
      rw [bytesAt_add, Proof.Rc2.bytesAt_frame hf _ _ (by omega)
        (by simpa using Offset.disjoint c (d := 136) (n := p) (by omega) (by omega) (by omega)),
        show (136 : Addr) = BitVec.ofNat 64 136 from rfl, Offset.add_add, hm,
        VG.Proof.Rc2.AArch64.Stream.bytesAt_writeBytes' _ _ _ _ (by omega)])
  refine ⟨r1, ?_⟩
  rw [olq]; exact r2

/-! ## Complete blocks -/

theorem prep_keeps : prep.allInstrs (fun i => preserved.all fun r => dstOf i != some r) = true := by
  decide +kernel

/-- `update` with complete blocks, without its frame. -/
theorem long_ok (d : Spec.Rc2.Direction) {σ : State} {c dp op b : Addr} {p len ol : Nat}
    (h : VG.Proof.Rc2.AArch64.Stream.Lay σ c dp op b p len ol) (hol : ol ≠ 0) :
    WP isa (longMain d) σ fun s' => (∀ r ∈ preserved, r ≠ .x30 → s'.gpr r = σ.gpr r) ∧
      VG.Proof.Rc2.AArch64.Stream.UPost d σ c dp op p len ol s' := by
  have p8 := h.p8
  have olq := h.olq
  have hl := h.lenlt
  have hpo : p ≤ ol := by omega
  unfold longMain
  refine WP.seq (WP.mono (WP.gprs (rs := preserved) (VG.Proof.Rc2.AArch64.Stream.prep_ok h hol) VG.Proof.Rc2.AArch64.Stream.prep_keeps (by decide +kernel)) fun s₁ ⟨hc, hk⟩ => ?_)
  refine VG.Proof.Rc2.AArch64.Stream.call_ok d hc.x0 hc.x1 hc.x2 hc.x3 hc.x4 (n := (p + len) / 8) (by omega) h.ollt
    (hc.rd.trans h.rd) (hc.wr.trans h.wr) h.co h.cb h.ob h.fo
    fun s' hrd hwr hsp hf hcs hout hiv => ⟨fun r hr h30 => (hcs r hr h30).trans (hk r hr), ?_⟩
  have hctx : ∀ {e n : Nat}, e + n ≤ 144 → Region.Sub ⟨c + BitVec.ofNat 64 e, n⟩ ⟨c, 144⟩ :=
    fun he => Offset.sub_base _ he
  have co' : ∀ {e n : Nat}, e + n ≤ 144 → Region.Disjoint ⟨c + BitVec.ofNat 64 e, n⟩ ⟨op, ol⟩ :=
    fun he => h.co.sub_left (hctx he)
  have cb' : ∀ {e n : Nat}, e + n ≤ 144 → Region.Disjoint ⟨c + BitVec.ofNat 64 e, n⟩ ⟨b, 512⟩ :=
    fun he => (h.cb.sub_left (hctx he)).sub_right (Region.sub_prefix (by omega))
  have co0 : Region.Disjoint ⟨c, 128⟩ ⟨op, ol⟩ := h.co.sub_left (Region.sub_prefix (by omega))
  have cb0 : Region.Disjoint ⟨c, 128⟩ ⟨b, 512⟩ :=
    (h.cb.sub_left (Region.sub_prefix (by omega))).sub_right (Region.sub_prefix (by omega))
  have outS : Region.Sub ⟨op, 8 * ((p + len) / 8)⟩ ⟨op, ol⟩ := Region.sub_prefix (by omega)
  have hr : len + p - ol = (p + len) % 8 := by omega
  have pend := hc.pend
  rw [hr, show ol - p = (p + len) / 8 * 8 - p by omega] at pend
  obtain ⟨r1, r2⟩ := update_post_long (d := d) (m₁ := s₁.mem) (out := op) (p := p) (len := len)
    (by omega) (by omega) (by rw [← olq]; exact hc.out)
    (scheduleAt_frame hc.frame c (by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro r (rfl | rfl)
      · exact co0.sub_right (Region.sub_prefix (Nat.le_refl _))
      · exact Offset.base_disjoint c (k := 128) (e := 136) (n := 8) (by omega) (by omega)))
    (blockAt_frame hc.frame (c + 128) (by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro r (rfl | rfl)
      · exact co' (e := 128) (by omega)
      · exact Offset.disjoint c (d := 128) (n := 8) (e := 136) (k := 8) (by omega) (by omega) (by omega)))
    (by
      rw [Proof.Rc2.bytesAt_frame hf _ _ (by omega) (by
        simp only [List.mem_cons, List.not_mem_nil, or_false]
        rintro r (rfl | rfl | rfl)
        · exact Offset.disjoint c (d := 136) (n := (p + len) % 8) (e := 128) (k := 8) (by omega) (by omega)
            (by omega)
        · exact (co' (e := 136) (n := (p + len) % 8) (by omega)).sub_right outS
        · exact cb' (e := 136) (n := (p + len) % 8) (by omega))]
      exact pend)
    (scheduleAt_frame hf c (by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro r (rfl | rfl | rfl)
      · exact Offset.base_disjoint c (k := 128) (e := 128) (n := 8) (by omega) (by omega)
      · exact co0.sub_right outS
      · exact cb0))
    hout hiv
  refine ⟨r1, ?_⟩
  rw [olq]; exact r2

/-! ## The whole update -/

theorem longMain_noFrames (d : Spec.Rc2.Direction) : (longMain d).noFrames = true := by
  cases d <;> decide +kernel

theorem update_correct (d : Spec.Rc2.Direction) (s₀ : State) (hs : (VG.Proof.Rc2.AArch64.Stream.updateContract d).pre s₀) :
    WP isa (update d) s₀ fun s' => GprAbi s₀ s' ∧ (VG.Proof.Rc2.AArch64.Stream.updateContract d).post s₀ s' := by
  obtain ⟨sp16, hrd, hwr, cd, co, cb, dout, db, ob, kc, kd, ko, kb, -, -, fo, -, p8, olq⟩ := hs
  have h : VG.Proof.Rc2.AArch64.Stream.Lay s₀ (s₀.gpr .x0) (s₀.gpr .x2) (s₀.gpr .x4) (s₀.gpr .x6) (s₀.gpr .x1).toNat
      (s₀.gpr .x3).toNat (s₀.gpr .x5).toNat :=
    ⟨rfl, VG.Proof.Rc2.AArch64.Stream.ofNat_toNat' _, rfl, VG.Proof.Rc2.AArch64.Stream.ofNat_toNat' _, rfl, VG.Proof.Rc2.AArch64.Stream.ofNat_toNat' _, rfl, hrd, hwr, cd, co, cb, dout, db,
      ob, fo, (s₀.gpr .x3).isLt, (s₀.gpr .x5).isLt, p8, olq⟩
  unfold update
  refine WP.ite (decide ((s₀.gpr .x5).toNat = 0))
    (by show VG.AArch64.eval (.zero .x .x5) s₀ = _
        have e := ofNat_beq_zero (s₀.gpr .x5).isLt
        rw [← h.x5] at e
        rw [VG.Proof.MdStream.AArch64.eval_zero, e]) (fun hb => ?_) (fun hb => ?_)
  · simp only [decide_eq_true_eq] at hb
    exact WP.mono (VG.Proof.Rc2.AArch64.Stream.short_ok d h hb) fun s' ⟨hk, hsp, hp⟩ => ⟨⟨hk, hsp⟩, hp⟩
  simp only [decide_eq_false_iff_not] at hb
  have hσ : VG.Proof.Rc2.AArch64.Stream.Lay (VG.Proof.Rc2.AArch64.Stream.inner s₀) (s₀.gpr .x0) (s₀.gpr .x2) (s₀.gpr .x4) (s₀.gpr .x6) (s₀.gpr .x1).toNat
      (s₀.gpr .x3).toNat (s₀.gpr .x5).toNat :=
    ⟨h.x0, h.x1, h.x2, h.x3, h.x4, h.x5, h.x6, h.rd, h.wr, cd, co, cb, dout, db, ob, fo, h.lenlt,
      h.ollt, p8, olq⟩
  refine WP.frameReg sp16 (fun R hR => ?_) (WP.mono (VG.Proof.Rc2.AArch64.Stream.long_ok d hσ hb) fun s₂ ⟨hk, hpost⟩ => ?_)
    (by rw [VG.Proof.Rc2.AArch64.Stream.fdepth_of_noFrames (VG.Proof.Rc2.AArch64.Stream.longMain_noFrames d)]; decide)
  · rw [hwr] at hR
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hR
    rcases hR with rfl | rfl | rfl
    · exact kc
    · exact ko
    · exact kb
  refine ⟨⟨fun r hr => ?_, rfl⟩, ?_⟩
  · by_cases h30 : r = .x30
    · subst h30; simp [State.write]
    · simp only [State.write, h30, ite_false]
      exact hk r hr h30
  · have hf := VG.Proof.Rc2.AArch64.Stream.frame_push s₀
    have hctx : ∀ {e n : Nat}, e + n ≤ 144 →
        ∀ r ∈ [(⟨s₀.sp - 16, 16⟩ : Region)], Region.Disjoint ⟨s₀.gpr .x0 + BitVec.ofNat 64 e, n⟩ r := by
      intro e n he r hr
      simp only [List.mem_singleton] at hr; subst hr
      exact (kc.sub_right (Offset.sub_base _ he)).symm
    have e₁ : Spec.Rc2.contextAt (VG.Proof.Rc2.AArch64.Stream.inner s₀).mem (s₀.gpr .x0) d (s₀.gpr .x1).toNat =
        Spec.Rc2.contextAt s₀.mem (s₀.gpr .x0) d (s₀.gpr .x1).toNat := by
      unfold Spec.Rc2.contextAt
      rw [VG.Proof.Rc2.AArch64.Stream.inner_mem, scheduleAt_frame hf _ (by simpa using hctx (e := 0) (n := 128) (by omega)),
        blockAt_frame hf (s₀.gpr .x0 + 128) (hctx (e := 128) (by omega)),
        Proof.Rc2.bytesAt_frame hf (s₀.gpr .x0 + 136) _ (by omega) (hctx (e := 136) (by omega))]
    have e₂ : Spec.Rc2.bytesAt (VG.Proof.Rc2.AArch64.Stream.inner s₀).mem (s₀.gpr .x2) (s₀.gpr .x3).toNat =
        Spec.Rc2.bytesAt s₀.mem (s₀.gpr .x2) (s₀.gpr .x3).toNat := by
      rw [VG.Proof.Rc2.AArch64.Stream.inner_mem]
      exact Proof.Rc2.bytesAt_frame hf _ _ (by omega) (by simpa using kd.symm)
    have hp : VG.Proof.Rc2.AArch64.Stream.UPost d (VG.Proof.Rc2.AArch64.Stream.inner s₀) (s₀.gpr .x0) (s₀.gpr .x2) (s₀.gpr .x4) (s₀.gpr .x1).toNat
      (s₀.gpr .x3).toNat (s₀.gpr .x5).toNat s₂ := hpost
    unfold VG.Proof.Rc2.AArch64.Stream.UPost at hp
    rw [e₁, e₂] at hp
    exact hp

end VG.Proof.Rc2.AArch64.Stream

end

/- Proofs formerly in `VerifiedGarbage.Proof.Rc2.AArch64.Stream.Verified`. -/
section

/-!
# Verified streaming RC2-CBC on AArch64

Correctness (`Init`, `Update`), constant time (`ConstantTime`), and states
satisfying the preconditions, moved to the shared contracts with `stack = 16`
(the frame saving `x30`).
-/

namespace VG.Proof.Rc2.AArch64.Stream

open VG VG.AArch64 VG.Impl.Rc2.AArch64.Stream

def initSat : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x3 => 0x2000 | .x5 => 0x3000 | .x6 => 0x4000 | _ => 0
  sp := 0x6000
  mem _ := 0
  rd := [⟨0x1000, 0⟩, ⟨0x2000, 0⟩]
  wr := [⟨0x3000, 144⟩, ⟨0x4000, 576⟩]

def updateSat : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x2 => 0x2000 | .x4 => 0x3000 | .x6 => 0x4000 | _ => 0
  sp := 0x6000
  mem _ := 0
  rd := [⟨0x2000, 0⟩]
  wr := [⟨0x1000, 144⟩, ⟨0x3000, 0⟩, ⟨0x4000, 576⟩]

theorem publicRegs_seven (s₁ s₂ : State) : PublicRegs [.x0, .x1, .x2, .x3, .x4, .x5, .x6] s₁ s₂ ↔
    s₁.sp = s₂.sp ∧ s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.gpr .x2 = s₂.gpr .x2 ∧
    s₁.gpr .x3 = s₂.gpr .x3 ∧ s₁.gpr .x4 = s₂.gpr .x4 ∧ s₁.gpr .x5 = s₂.gpr .x5 ∧
    s₁.gpr .x6 = s₂.gpr .x6 := by
  simp [PublicRegs]

theorem init_correct' (s : State) (hs : initContract.pre s) :
    ∃ t s', Exec isa init s t s' ∧ abiPreserved s s' ∧ initContract.post s s' :=
  WP.withPreservedV (VG.Proof.Rc2.AArch64.Stream.init_correct s hs) (by lit_decide)

theorem encryptUpdate_correct (s : State) (hs : (VG.Proof.Rc2.AArch64.Stream.updateContract .encrypt).pre s) :
    ∃ t s', Exec isa encryptUpdate s t s' ∧ abiPreserved s s' ∧ (VG.Proof.Rc2.AArch64.Stream.updateContract .encrypt).post s s' :=
  WP.withPreservedV (VG.Proof.Rc2.AArch64.Stream.update_correct .encrypt s hs)
    (by lit_decide)

theorem decryptUpdate_correct (s : State) (hs : (VG.Proof.Rc2.AArch64.Stream.updateContract .decrypt).pre s) :
    ∃ t s', Exec isa decryptUpdate s t s' ∧ abiPreserved s s' ∧ (VG.Proof.Rc2.AArch64.Stream.updateContract .decrypt).post s s' :=
  WP.withPreservedV (VG.Proof.Rc2.AArch64.Stream.update_correct .decrypt s hs)
    (by lit_decide)

theorem init_verified : Verified target init (Proof.Rc2.cbcInitScratchContract abi 16) := by
  refine Verified.of_correct VG.Proof.Rc2.AArch64.Stream.init_correct' (VG.Proof.Rc2.AArch64.Stream.init_constantTime _) ?_
  sig_implies [Proof.Rc2.cbcInitScratchContract, Proof.Rc2.cbcInitScratchSig, Spec.Rc2.cbcInitPost, abi, argRegs, VG.Proof.Rc2.AArch64.Stream.initContract,
    VG.Proof.Rc2.AArch64.Stream.publicRegs_seven] [initSat] using VG.Proof.Rc2.AArch64.Stream.initSat

theorem encryptUpdate_verified :
    Verified target encryptUpdate (Proof.Rc2.cbcEncryptUpdateScratchContract abi 16) := by
  refine Verified.of_correct VG.Proof.Rc2.AArch64.Stream.encryptUpdate_correct (VG.Proof.Rc2.AArch64.Stream.encryptUpdate_constantTime _) ?_
  sig_implies [Proof.Rc2.cbcEncryptUpdateScratchContract, Proof.Rc2.cbcUpdateScratchContract, Proof.Rc2.cbcUpdateScratchSig, Spec.Rc2.cbcUpdatePre, Spec.Rc2.cbcUpdatePost,
    abi, argRegs, VG.Proof.Rc2.AArch64.Stream.updateContract, VG.Proof.Rc2.AArch64.Stream.publicRegs_seven] [updateSat] using VG.Proof.Rc2.AArch64.Stream.updateSat

theorem decryptUpdate_verified :
    Verified target decryptUpdate (Proof.Rc2.cbcDecryptUpdateScratchContract abi 16) := by
  refine Verified.of_correct VG.Proof.Rc2.AArch64.Stream.decryptUpdate_correct (VG.Proof.Rc2.AArch64.Stream.decryptUpdate_constantTime _) ?_
  sig_implies [Proof.Rc2.cbcDecryptUpdateScratchContract, Proof.Rc2.cbcUpdateScratchContract, Proof.Rc2.cbcUpdateScratchSig, Spec.Rc2.cbcUpdatePre, Spec.Rc2.cbcUpdatePost,
    abi, argRegs, VG.Proof.Rc2.AArch64.Stream.updateContract, VG.Proof.Rc2.AArch64.Stream.publicRegs_seven] [updateSat] using VG.Proof.Rc2.AArch64.Stream.updateSat

end VG.Proof.Rc2.AArch64.Stream

end

/- Proofs formerly in `VerifiedGarbage.Proof.Rc2.AArch64.Stream.Frame`. -/
section

/-!
# RC2-CBC's streaming functions on AArch64, with their working space on the stack

`init` and the updates run their code, proved with the working space as an
argument (`Verified.lean`), in a frame of 576 bytes that allocates it
(`Verified.stackScratchWiped`), and zero it before returning.
-/

namespace VG.Proof.Rc2.AArch64.Stream

open VG VG.AArch64 VG.Impl.Rc2.AArch64.Stream

/-- A state satisfying `vg_rc2_cbc_init`'s precondition, without the working
space. -/
def initFrameSat : State := { VG.Proof.Rc2.AArch64.Stream.initSat with
                                           wr := [⟨0x3000, 144⟩] }

theorem initFrameSat_pre : ∃ s, (Spec.Rc2.cbcInitContract AArch64.abi 592).pre s := by
  implies_sat [Spec.Rc2.cbcInitContract, Spec.Rc2.cbcInitSig, Spec.Rc2.cbcInitPost, AArch64.abi,
    AArch64.argRegs] [initFrameSat, initSat] using VG.Proof.Rc2.AArch64.Stream.initFrameSat

theorem init_framed :
    Verified AArch64.target (Impl.StackScratch.AArch64.withStackScratchWiped 576 .x6 72 init)
      (Spec.Rc2.cbcInitContract AArch64.abi 592) :=
  AArch64.Verified.stackScratchWiped (sig := Spec.Rc2.cbcInitSig) (nm := "scratch") (e := .u64)
    (n := 72) (post := Spec.Rc2.cbcInitPost AArch64.abi.ptrBits) (wa := true) (stack := 16)
    (bytes := 576) (words := 72) VG.Proof.Rc2.AArch64.Stream.init_verified (by decide) (by decide) (by decide)
    (cbcInitPostOut_local _) VG.Proof.Rc2.AArch64.Stream.initFrameSat_pre

/-- A state satisfying the update functions' precondition, without the
working space. -/
def updateFrameSat : State := { VG.Proof.Rc2.AArch64.Stream.updateSat with
                                               wr := [⟨0x1000, 144⟩, ⟨0x3000, 0⟩] }

theorem updateFrameSat_pre (d : Spec.Rc2.Direction) :
    ∃ s, (Spec.Rc2.cbcUpdateContract AArch64.abi d 592).pre s := by
  implies_sat [Spec.Rc2.cbcUpdateContract, Spec.Rc2.cbcUpdateSig, Spec.Rc2.cbcUpdatePre,
    Spec.Rc2.cbcUpdatePost, AArch64.abi, AArch64.argRegs] [updateFrameSat, updateSat]
    using VG.Proof.Rc2.AArch64.Stream.updateFrameSat

theorem encryptUpdate_framed :
    Verified AArch64.target (Impl.StackScratch.AArch64.withStackScratchWiped 576 .x6 72 encryptUpdate)
      (Spec.Rc2.cbcEncryptUpdateContract AArch64.abi 592) :=
  AArch64.Verified.stackScratchWiped (sig := Spec.Rc2.cbcUpdateSig) (nm := "scratch") (e := .u64)
    (n := 72) (pre := Spec.Rc2.cbcUpdatePre AArch64.abi.ptrBits)
    (post := Spec.Rc2.cbcUpdatePost .encrypt AArch64.abi.ptrBits) (wa := true) (stack := 16)
    (bytes := 576) (words := 72) VG.Proof.Rc2.AArch64.Stream.encryptUpdate_verified (by decide) (by decide) (by decide)
    (cbcUpdatePostOut_local _ _) (VG.Proof.Rc2.AArch64.Stream.updateFrameSat_pre .encrypt)

theorem decryptUpdate_framed :
    Verified AArch64.target (Impl.StackScratch.AArch64.withStackScratchWiped 576 .x6 72 decryptUpdate)
      (Spec.Rc2.cbcDecryptUpdateContract AArch64.abi 592) :=
  AArch64.Verified.stackScratchWiped (sig := Spec.Rc2.cbcUpdateSig) (nm := "scratch") (e := .u64)
    (n := 72) (pre := Spec.Rc2.cbcUpdatePre AArch64.abi.ptrBits)
    (post := Spec.Rc2.cbcUpdatePost .decrypt AArch64.abi.ptrBits) (wa := true) (stack := 16)
    (bytes := 576) (words := 72) VG.Proof.Rc2.AArch64.Stream.decryptUpdate_verified (by decide) (by decide) (by decide)
    (cbcUpdatePostOut_local _ _) (VG.Proof.Rc2.AArch64.Stream.updateFrameSat_pre .decrypt)

end VG.Proof.Rc2.AArch64.Stream

end
