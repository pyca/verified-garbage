module
import VerifiedGarbage.Proof.Scrypt.AArch64.Transfer.Packet
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Scrypt.Memory
import VerifiedGarbage.Proof.MdStream.AArch64.Common
import VerifiedGarbage.Proof.Scrypt.AArch64.Transfer.Memory
public import VerifiedGarbage.Impl.MdStream.AArch64
public import VerifiedGarbage.Impl.Scrypt.AArch64.Transfer
public import VerifiedGarbage.Proof.Framework.AArch64.Inline
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Framework.WriteBytes
public import VerifiedGarbage.Proof.MdStream.Spec
public import VerifiedGarbage.Proof.Sha256.Stream
public import VerifiedGarbage.Spec.Scrypt.Contract
public import VerifiedGarbage.TCB.AArch64.Isa

@[expose] public section
namespace VG.Proof.Scrypt.AArch64.RoMix
open VG VG.AArch64
open VG.Spec.Scrypt (bytesAt)
open VG.Spec.Pbkdf2 (xorBytes)
open VG.Proof.Sha256.Stream (writeBytes writeBytes_nil)
open VG.Proof.MdStream.AArch64 (wp_addImm wp_subImm eval_nonzero ofNat_beq_zero ofNat_pred)
open VG.Proof.Scrypt.Memory (toNat_ofNat_lt add_ofNat)
theorem add_zero' (p : Addr) : p + BitVec.ofNat 64 0 = p := BitVec.add_zero _

/-- A pointer advanced by one word. -/
theorem next_ptr (p : Addr) (k : Nat) :
    p + BitVec.ofNat 64 (8 * k) + BitVec.ofNat 64 8 = p + BitVec.ofNat 64 (8 * (k + 1)) := by
  rw [add_ofNat, Nat.mul_succ]

/-- The count after one more iteration of `n`. -/
theorem dec_count {n k : Nat} (hk : k < n) :
    BitVec.ofNat 64 (n - k) - BitVec.ofNat 64 1 = BitVec.ofNat 64 (n - (k + 1)) := by
  rw [show BitVec.ofNat 64 1 = 1 from rfl, ofNat_pred (by omega_arith), Nat.sub_sub]

theorem dec_ne {n k : Nat} (hk : k < n) (hn : n < 2 ^ 64) :
    (BitVec.ofNat 64 (n - (k + 1)) != 0) = decide (k + 1 ≠ n) := by
  rw [bne, ofNat_beq_zero (by omega_arith)]
  by_cases h : k + 1 = n
  · simp only [h, Nat.sub_self, decide_true, Bool.not_true, ne_eq, not_true_eq_false, decide_false]
  · simp only [show n - (k + 1) ≠ 0 by omega_arith, decide_false, Bool.not_false, ne_eq, h,
      not_false_eq_true, decide_true]

theorem ofNat_zero_add (p : Addr) : p + BitVec.ofNat 64 (8 * 0) = p := by
  rw [Nat.mul_zero]; exact BitVec.add_zero _

/-! ## Counted loops -/

/-- A do-while loop on `cbnz cr` that runs its body `n > 0` times: the
register is zero exactly after the last iteration. -/
theorem count_loop {body : Prog isa} {cr : Reg} {n : Nat} (hn : 0 < n) (I : Nat → State → Prop)
    (hstep : ∀ k < n, ∀ s, I k s →
      WP isa body s fun s' => I (k + 1) s' ∧ (s'.gpr cr != 0) = decide (k + 1 ≠ n))
    {s : State} (h0 : I 0 s) : WP isa (.loop body (.nonzero .x cr)) s (I n) := by
  refine WP.loop (M := isa) (fun m s => ∃ k, m = n - k ∧ k < n ∧ I k s) ?_ n s ⟨0, by omega_arith, hn, h0⟩
  rintro m s ⟨k, rfl, hk, hi⟩
  refine WP.mono (hstep k hk s hi) fun s' ⟨hi', hc⟩ => ?_
  have hz : isa.eval (.nonzero .x cr) s' = some (decide (k + 1 ≠ n)) := by
    show VG.AArch64.eval (.nonzero .x cr) s' = _
    rw [eval_nonzero, hc]
  by_cases hl : k + 1 = n
  · refine .inl ⟨by rw [hz]; simp [hl], ?_⟩
    rwa [hl] at hi'
  · exact .inr ⟨by rw [hz]; simp [hl], n - (k + 1), by omega_arith, k + 1, rfl, by omega_arith, hi'⟩


theorem in_packet {rs : List Region} {p : Addr} (h : InRegions rs p 64) {j : Nat} (hj : j < 4) :
    InRegions rs (p + BitVec.ofNat 64 (16*j)) 16 := by
  obtain ⟨r,hr,hc⟩ := h
  refine ⟨r,hr,?_⟩
  have e : p + BitVec.ofNat 64 (16*j) - r.base = (p-r.base) + BitVec.ofNat 64 (16*j) := by bv_omega
  have le : (p + BitVec.ofNat 64 (16*j) - r.base).toNat ≤ (p-r.base).toNat + 16*j := by
    rw [e,BitVec.toNat_add,toNat_ofNat_lt (by omega)]
    exact Nat.mod_le _ _
  simp only [Region.Contains] at hc ⊢
  omega

theorem next_packet (p : Addr) (k : Nat) :
    p + BitVec.ofNat 64 (64*k) + BitVec.ofNat 64 64 = p + BitVec.ofNat 64 (64*(k+1)) := by
  rw [add_ofNat,Nat.mul_succ]

theorem packet_count {n k : Nat} (hk : k < n) :
    BitVec.ofNat 64 (8*(n-k)) - BitVec.ofNat 64 8 = BitVec.ofNat 64 (8*(n-(k+1))) := by
  rw [VG.Proof.MdStream.AArch64.sub_ofNat (by omega)]
  congr 1; omega

theorem packet_ne {n k : Nat} (hk : k < n) (hn : 64*n < 2^64) :
    (BitVec.ofNat 64 (8*(n-(k+1))) != 0) = decide (k+1 ≠ n) := by
  rw [bne,ofNat_beq_zero (by omega)]
  by_cases h : k+1 = n
  · simp [h]
  · simp [show 8*(n-(k+1)) ≠ 0 by omega,h]

structure CopyInv (s : State) (src dst : Addr) (n k : Nat) (t : State) : Prop where
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp
  other : ∀ r, r ≠ .x9 → r ≠ .x10 → r ≠ .x11 → r ≠ .x12 → t.gpr r = s.gpr r
  x9 : t.gpr .x9 = src + BitVec.ofNat 64 (64*k)
  x10 : t.gpr .x10 = dst + BitVec.ofNat 64 (64*k)
  x11 : t.gpr .x11 = BitVec.ofNat 64 (8*(n-k))
  mem : t.mem = writeBytes s.mem dst (bytesAt s.mem src (64*k))

theorem copy_step {s : State} {src dst : Addr} {n : Nat} (hlt : 64*n < 2^64)
    (hin : ∀ k < n, InRegions (s.rd ++ s.wr) (src + BitVec.ofNat 64 (64*k)) 64)
    (hout : ∀ k < n, InRegions s.wr (dst + BitVec.ofNat 64 (64*k)) 64)
    (hsep : Region.Disjoint ⟨src,64*n⟩ ⟨dst,64*n⟩) {k : Nat} (hk : k < n) {t : State}
    (h : CopyInv s src dst n k t) :
    WP isa (.block (VG.Impl.Scrypt.AArch64.Transfer.copyPacket ++
      ([.addImm .x .x9 .x9 64,.addImm .x .x10 .x10 64,.subImm .x .x11 .x11 8] : List Instr))) t
      fun t' => CopyInv s src dst n (k+1) t' ∧ (t'.gpr .x11 != 0) = decide (k+1 ≠ n) := by
  apply WP.block_append
  refine WP.mono (Transfer.copyPacket_ok t
    (by intro j hj; rw [h.rd,h.wr,h.x9]; exact in_packet (hin k hk) hj)
    (by intro j hj; rw [h.wr,h.x10]; exact in_packet (hout k hk) hj))
    fun a ⟨ga,ra,wa,sa,ma⟩ => ?_
  refine wp_addImm (by decide) fun b ub => wp_addImm (by decide) fun c uc =>
    wp_subImm (by decide) fun d ud => WP.block_nil ?_
  have ec : d.gpr .x11 = BitVec.ofNat 64 (8*(n-(k+1))) := by
    rw [ud.gpr,uc.other _ (by decide),ub.other _ (by decide),ga,h.x11,packet_count hk]
  refine ⟨⟨ud.rd.trans (uc.rd.trans (ub.rd.trans (ra.trans h.rd))),
    ud.wr.trans (uc.wr.trans (ub.wr.trans (wa.trans h.wr))),
    ud.sp.trans (uc.sp.trans (ub.sp.trans (sa.trans h.sp))),?_,?_,?_,ec,?_⟩,?_⟩
  · intro r h9 h10 h11 h12
    rw [ud.other r h11,uc.other r h10,ub.other r h9,ga,h.other r h9 h10 h11 h12]
  · rw [ud.other _ (by decide),uc.other _ (by decide),ub.gpr,ga,h.x9,next_packet]
  · rw [ud.other _ (by decide),uc.gpr,ub.other _ (by decide),ga,h.x10,next_packet]
  · rw [ud.mem,uc.mem,ub.mem,ma,h.x9,h.x10,h.mem]
    have e := VG.Proof.Scrypt.Memory.copy_mem s.mem src dst k 64
      (hsep.sep (by simp only [Region.Contains,BitVec.sub_self,BitVec.toNat_zero]; omega)
        (by simp only [Region.Contains,BitVec.sub_self,BitVec.toNat_zero]; omega)) (by omega)
    rw [VG.Proof.Scrypt.Memory.writeW_readW _ _ _ _ 64] at e
    simpa only [Nat.mul_succ] using e
  · rw [ec,packet_ne hk hlt]

theorem copyLoop_ok {s : State} {src dst : Addr} {n : Nat} (hn : 0 < n) (hlt : 64*n < 2^64)
    (h9 : s.gpr .x9 = src) (h10 : s.gpr .x10 = dst) (h11 : s.gpr .x11 = BitVec.ofNat 64 (8*n))
    (hin : ∀ k < n, InRegions (s.rd ++ s.wr) (src + BitVec.ofNat 64 (64*k)) 64)
    (hout : ∀ k < n, InRegions s.wr (dst + BitVec.ofNat 64 (64*k)) 64)
    (hsep : Region.Disjoint ⟨src,64*n⟩ ⟨dst,64*n⟩) :
    WP isa VG.Impl.Scrypt.AArch64.Transfer.copyLoop s fun s' =>
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
      (∀ r, r ≠ .x9 → r ≠ .x10 → r ≠ .x11 → r ≠ .x12 → s'.gpr r = s.gpr r) ∧
      s'.mem = writeBytes s.mem dst (bytesAt s.mem src (64*n)) := by
  refine WP.mono (count_loop hn (CopyInv s src dst n)
    (fun k hk t h => copy_step hlt hin hout hsep hk h) ?_) fun t h => ⟨h.rd,h.wr,h.sp,h.other,h.mem⟩
  exact ⟨rfl,rfl,rfl,fun _ _ _ _ _ => rfl,by simpa using h9,by simpa using h10,
    by simpa using h11,by simp [bytesAt,writeBytes_nil]⟩
structure XorInv (s : State) (x y d : Addr) (n k : Nat) (t : State) : Prop where
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp
  other : ∀ r, r ≠ .x9 → r ≠ .x10 → r ≠ .x11 → r ≠ .x12 → r ≠ .x13 → r ≠ .x14 → t.gpr r = s.gpr r
  x9 : t.gpr .x9 = x + BitVec.ofNat 64 (64*k)
  x10 : t.gpr .x10 = y + BitVec.ofNat 64 (64*k)
  x11 : t.gpr .x11 = d + BitVec.ofNat 64 (64*k)
  x12 : t.gpr .x12 = BitVec.ofNat 64 (8*(n-k))
  mem : t.mem = writeBytes s.mem d (xorBytes (bytesAt s.mem x (64*k)) (bytesAt s.mem y (64*k)))

theorem xor_step {s : State} {x y d : Addr} {n : Nat} (hlt : 64*n < 2^64)
    (hinx : ∀ k < n, InRegions (s.rd ++ s.wr) (x + BitVec.ofNat 64 (64*k)) 64)
    (hiny : ∀ k < n, InRegions (s.rd ++ s.wr) (y + BitVec.ofNat 64 (64*k)) 64)
    (hout : ∀ k < n, InRegions s.wr (d + BitVec.ofNat 64 (64*k)) 64)
    (hdx : Region.Disjoint ⟨d,64*n⟩ ⟨x,64*n⟩) (hdy : Region.Disjoint ⟨d,64*n⟩ ⟨y,64*n⟩)
    {k : Nat} (hk : k < n) {t : State} (h : XorInv s x y d n k t) :
    WP isa (.block (VG.Impl.Scrypt.AArch64.Transfer.xorPacket ++
      ([.addImm .x .x9 .x9 64,.addImm .x .x10 .x10 64,.addImm .x .x11 .x11 64,.subImm .x .x12 .x12 8] : List Instr))) t
      fun t' => XorInv s x y d n (k+1) t' ∧ (t'.gpr .x12 != 0) = decide (k+1 ≠ n) := by
  apply WP.block_append
  refine WP.mono (Transfer.xorPacket_ok t
    (by intro j hj; rw [h.rd,h.wr,h.x9]; exact in_packet (hinx k hk) hj)
    (by intro j hj; rw [h.rd,h.wr,h.x10]; exact in_packet (hiny k hk) hj)
    (by intro j hj; rw [h.wr,h.x11]; exact in_packet (hout k hk) hj))
    fun a ⟨ga,ra,wa,sa,ma⟩ => ?_
  refine wp_addImm (by decide) fun b ub => wp_addImm (by decide) fun c uc =>
    wp_addImm (by decide) fun e ue => wp_subImm (by decide) fun f uf => WP.block_nil ?_
  have ec : f.gpr .x12 = BitVec.ofNat 64 (8*(n-(k+1))) := by
    rw [uf.gpr,ue.other _ (by decide),uc.other _ (by decide),ub.other _ (by decide),ga,h.x12,packet_count hk]
  refine ⟨⟨uf.rd.trans (ue.rd.trans (uc.rd.trans (ub.rd.trans (ra.trans h.rd)))),
    uf.wr.trans (ue.wr.trans (uc.wr.trans (ub.wr.trans (wa.trans h.wr)))),
    uf.sp.trans (ue.sp.trans (uc.sp.trans (ub.sp.trans (sa.trans h.sp)))),?_,?_,?_,?_,ec,?_⟩,?_⟩
  · intro r h9 h10 h11 h12 h13 h14
    rw [uf.other r h12,ue.other r h11,uc.other r h10,ub.other r h9,ga,h.other r h9 h10 h11 h12 h13 h14]
  · rw [uf.other _ (by decide),ue.other _ (by decide),uc.other _ (by decide),ub.gpr,ga,h.x9,next_packet]
  · rw [uf.other _ (by decide),ue.other _ (by decide),uc.gpr,ub.other _ (by decide),ga,h.x10,next_packet]
  · rw [uf.other _ (by decide),ue.gpr,uc.other _ (by decide),ub.other _ (by decide),ga,h.x11,next_packet]
  · rw [uf.mem,ue.mem,uc.mem,ub.mem,ma,h.x9,h.x10,h.x11,h.mem]
    have eq := Transfer.xor_mem 64 s.mem hk hlt hdx hdy
    rw [Transfer.writeW_xor 64] at eq
    exact eq
  · rw [ec,packet_ne hk hlt]

theorem xorLoop_ok {s : State} {x y d : Addr} {n : Nat} (hn : 0 < n) (hlt : 64*n < 2^64)
    (h9 : s.gpr .x9 = x) (h10 : s.gpr .x10 = y) (h11 : s.gpr .x11 = d)
    (h12 : s.gpr .x12 = BitVec.ofNat 64 (8*n))
    (hinx : ∀ k < n, InRegions (s.rd ++ s.wr) (x + BitVec.ofNat 64 (64*k)) 64)
    (hiny : ∀ k < n, InRegions (s.rd ++ s.wr) (y + BitVec.ofNat 64 (64*k)) 64)
    (hout : ∀ k < n, InRegions s.wr (d + BitVec.ofNat 64 (64*k)) 64)
    (hdx : Region.Disjoint ⟨d,64*n⟩ ⟨x,64*n⟩) (hdy : Region.Disjoint ⟨d,64*n⟩ ⟨y,64*n⟩) :
    WP isa VG.Impl.Scrypt.AArch64.Transfer.xorLoop s fun s' =>
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
      (∀ r, r ≠ .x9 → r ≠ .x10 → r ≠ .x11 → r ≠ .x12 → r ≠ .x13 → r ≠ .x14 → s'.gpr r = s.gpr r) ∧
      s'.mem = writeBytes s.mem d (xorBytes (bytesAt s.mem x (64*n)) (bytesAt s.mem y (64*n))) := by
  refine WP.mono (count_loop hn (XorInv s x y d n)
    (fun k hk t h => xor_step hlt hinx hiny hout hdx hdy hk h) ?_)
    fun t h => ⟨h.rd,h.wr,h.sp,h.other,h.mem⟩
  exact ⟨rfl,rfl,rfl,fun _ _ _ _ _ _ _ => rfl,by simpa using h9,by simpa using h10,by simpa using h11,
    by simpa using h12,by simp [bytesAt,xorBytes,writeBytes_nil]⟩
end VG.Proof.Scrypt.AArch64.RoMix
