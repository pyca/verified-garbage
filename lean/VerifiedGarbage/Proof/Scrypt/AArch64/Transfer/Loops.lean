module
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Sha256.Stream
public import VerifiedGarbage.Impl.Scrypt.AArch64.Transfer
import VerifiedGarbage.Proof.Scrypt.AArch64.Transfer.Memory
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Scrypt.Memory
public import VerifiedGarbage.Proof.Framework.WriteBytes
public import VerifiedGarbage.Spec.Scrypt.Contract
import VerifiedGarbage.Proof.MdStream.AArch64.Common
public import VerifiedGarbage.Impl.MdStream.AArch64
public import VerifiedGarbage.Proof.Framework.AArch64.Inline
public import VerifiedGarbage.Proof.MdStream.Spec
public import VerifiedGarbage.TCB.AArch64.Isa

/-! ### `Scrypt.AArch64.Transfer.Packet`, which only this module used -/

section

@[expose] public section
namespace VG.Proof.Scrypt.AArch64.Transfer
open VG VG.AArch64 VG.Spec.Scrypt
open VG.Impl.Scrypt.AArch64.Transfer (vr)
open VG.Proof.Scrypt.Memory (add_ofNat sub_off)
open VG.Proof.Sha256.Stream (writeBytes writeBytes_frame)

theorem vr_ne {i j : Nat} (hi : i < 8) (hj : j < 8) (h : i ≠ j) : vr i ≠ vr j := by
  have key : ∀ i, i < 8 → ∀ j, j < 8 → i ≠ j → vr i ≠ vr j := by decide
  exact key i hi j hj h

theorem exec_loadQ {s : State} {t : VReg} {b : Reg} {off : Nat}
    (ho : off % 16 = 0 ∧ off < 65536)
    (hi : InRegions (s.rd ++ s.wr) (s.gpr b + BitVec.ofNat 64 off) 16) :
    exec (.ldrq t b off) s = some (s.setV t (s.mem.readW (s.gpr b + BitVec.ofNat 64 off) 128)) := by
  simp only [exec,VG.AArch64.addr,show off < 4096*16 by omega_using [ho],ho,and_self,ite_true,
    Option.bind_some,State.load,hi,Option.map_some,Mem.readW,BitVec.setWidth_eq]

theorem exec_storeQ {s : State} {t : VReg} {b : Reg} {off : Nat}
    (ho : off % 16 = 0 ∧ off < 65536)
    (hi : InRegions s.wr (s.gpr b + BitVec.ofNat 64 off) 16) :
    exec (.strq t b off) s = some {s with mem := s.mem.writeW (s.gpr b + BitVec.ofNat 64 off) (s.v t)} := by
  simp only [exec,VG.AArch64.addr,show off < 4096*16 by omega_using [ho],ho,and_self,ite_true,
    Option.bind_some,State.store,hi,Mem.writeW,BitVec.setWidth_eq]

theorem exec_xorQ {s : State} {d n m : VReg} :
    exec (.vop (.logic .eor d n m)) s = some (s.setV d (s.v n ^^^ s.v m)) := rfl

structure LI (s₀ : State) (b : Reg) (v i : Nat) (s : State) : Prop where
  gpr : s.gpr = s₀.gpr
  mem : s.mem = s₀.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  loaded : ∀ j < 4, j < i → s.v (vr (v+j)) = s₀.mem.readW (s₀.gpr b + BitVec.ofNat 64 (16*j)) 128
  keep : ∀ r, (∀ j < i, r ≠ vr (v+j)) → s.v r = s₀.v r

theorem load_step {s₀ s : State} {b : Reg} {v i : Nat} (hv : v = 0 ∨ v = 4) (hi : i < 4)
    (hin : ∀ j < 4, InRegions (s₀.rd ++ s₀.wr) (s₀.gpr b + BitVec.ofNat 64 (16*j)) 16)
    (h : LI s₀ b v i s) :
    WP isa (.block [.ldrq (vr (v+i)) b (16*i)]) s (LI s₀ b v (i+1)) := by
  have ir : InRegions (s.rd ++ s.wr) (s.gpr b + BitVec.ofNat 64 (16*i)) 16 := by
    rw [h.rd,h.wr,h.gpr]; exact hin i hi
  apply WP.of_runBlock
  simp only [runBlock_cons,runStep_some,runBlock_nil,
    exec_loadQ (show 16*i % 16 = 0 ∧ 16*i < 65536 by omega_using [hi]) ir,
    isa,Option.some.injEq,exists_eq_left']
  refine ⟨h.gpr,h.mem,h.rd,h.wr,h.sp,?_,?_⟩
  · intro j hj hji
    rcases Nat.lt_succ_iff_lt_or_eq.mp hji with lt | rfl
    · have ne : vr (v+j) ≠ vr (v+i) := vr_ne (by rcases hv with rfl | rfl <;> omega_using [hj])
        (by rcases hv with rfl | rfl <;> omega_using [hi]) (by omega_using [lt])
      simp only [State.setV,ne,ite_false]
      exact h.loaded j hj lt
    · simp only [State.setV,ite_true,h.mem,h.gpr]
  · intro r hr
    simp only [State.setV,hr i (by omega_using []),ite_false]
    exact h.keep r fun j hj => hr j (by omega_using [hj])

theorem loads_ok {s₀ : State} {b : Reg} {v : Nat} (hv : v = 0 ∨ v = 4)
    (hin : ∀ j < 4, InRegions (s₀.rd ++ s₀.wr) (s₀.gpr b + BitVec.ofNat 64 (16*j)) 16) :
    WP isa (.block (VG.Impl.Scrypt.AArch64.Transfer.loads b v)) s₀ (LI s₀ b v 4) := by
  have eq : VG.Impl.Scrypt.AArch64.Transfer.loads b v =
      (List.range 4).flatMap (fun j => [.ldrq (vr (v+j)) b (16*j)]) := by
    rfl
  rw [eq]
  exact wp_range_flatMap (M := isa) (LI s₀ b v) (fun i s hi h => load_step hv hi hin h)
    4 (by omega_using []) s₀ ⟨rfl,rfl,rfl,rfl,rfl,fun _ _ h => by omega,fun _ _ => rfl⟩
def writeQ4 (m : Mem) (d : Addr) (f : Nat → BitVec 128) : Mem :=
  (((m.writeW (d + BitVec.ofNat 64 (16*0)) (f 0)).writeW (d + BitVec.ofNat 64 (16*1)) (f 1)).writeW
    (d + BitVec.ofNat 64 (16*2)) (f 2)).writeW (d + BitVec.ofNat 64 (16*3)) (f 3)

structure Stored (s₀ : State) (b : Reg) (s : State) : Prop where
  gpr : s.gpr = s₀.gpr
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  mem : s.mem = writeQ4 s₀.mem (s₀.gpr b) (fun j => s₀.v (vr j))

theorem stores_ok (s₀ : State) (b : Reg)
    (hout : ∀ j < 4, InRegions s₀.wr (s₀.gpr b + BitVec.ofNat 64 (16*j)) 16) :
    WP isa (.block (VG.Impl.Scrypt.AArch64.Transfer.stores b)) s₀ (Stored s₀ b) := by
  change WP isa (.block [.strq (vr 0) b 0,.strq (vr 1) b 16,.strq (vr 2) b 32,.strq (vr 3) b 48]) s₀ _
  let s₁ : State := {s₀ with mem := s₀.mem.writeW (s₀.gpr b + BitVec.ofNat 64 0) (s₀.v (vr 0))}
  let s₂ : State := {s₁ with mem := s₁.mem.writeW (s₀.gpr b + BitVec.ofNat 64 16) (s₀.v (vr 1))}
  let s₃ : State := {s₂ with mem := s₂.mem.writeW (s₀.gpr b + BitVec.ofNat 64 32) (s₀.v (vr 2))}
  let s₄ : State := {s₃ with mem := s₃.mem.writeW (s₀.gpr b + BitVec.ofNat 64 48) (s₀.v (vr 3))}
  refine WP.block_cons_iff.mpr ⟨s₁,exec_storeQ (s := s₀) (by decide) (hout 0 (by omega_using [])),?_⟩
  refine WP.block_cons_iff.mpr ⟨s₂,exec_storeQ (s := s₁) (by decide) (hout 1 (by omega_using [])),?_⟩
  refine WP.block_cons_iff.mpr ⟨s₃,exec_storeQ (s := s₂) (by decide) (hout 2 (by omega_using [])),?_⟩
  refine WP.block_cons_iff.mpr ⟨s₄,exec_storeQ (s := s₃) (by decide) (hout 3 (by omega_using [])),?_⟩
  exact WP.block_nil ⟨rfl,rfl,rfl,rfl,rfl⟩

theorem writeQ4_copy (m m' : Mem) (d a : Addr) :
    writeQ4 m d (fun j => m'.readW (a + BitVec.ofNat 64 (16*j)) 128) =
      writeBytes m d (bytesAt m' a 64) := by
  simp only [writeQ4,Nat.reduceMul,BitVec.add_zero]
  rw [VG.Proof.Scrypt.Memory.writeW_readW m m' d a 16,
    VG.Proof.Scrypt.Memory.writeW_readW _ m' (d + BitVec.ofNat 64 16) (a + BitVec.ofNat 64 16) 16,
    VG.Proof.Scrypt.Memory.writeW_readW _ m' (d + BitVec.ofNat 64 32) (a + BitVec.ofNat 64 32) 16,
    VG.Proof.Scrypt.Memory.writeW_readW _ m' (d + BitVec.ofNat 64 48) (a + BitVec.ofNat 64 48) 16]
  have join (n : Nat) (hn : n ≤ 48) :
      writeBytes (writeBytes m d (bytesAt m' a n)) (d + BitVec.ofNat 64 n)
        (bytesAt m' (a + BitVec.ofNat 64 n) 16) = writeBytes m d (bytesAt m' a (n+16)) := by
    rw [VG.Proof.Scrypt.Memory.bytesAt_add]
    simpa only [VG.Proof.Scrypt.Memory.bytesAt_length] using
      VG.Proof.Sha256.Stream.writeBytes_append m d (bytesAt m' a n)
        (bytesAt m' (a + BitVec.ofNat 64 n) 16) (by simp [bytesAt]; omega_using [hn])
  rw [join 16 (by omega_using []),join 32 (by omega_using []),join 48 (by omega_using [])]

theorem copyPacket_ok (s₀ : State)
    (hin : ∀ j < 4, InRegions (s₀.rd ++ s₀.wr) (s₀.gpr .x9 + BitVec.ofNat 64 (16*j)) 16)
    (hout : ∀ j < 4, InRegions s₀.wr (s₀.gpr .x10 + BitVec.ofNat 64 (16*j)) 16) :
    WP isa (.block VG.Impl.Scrypt.AArch64.Transfer.copyPacket) s₀ fun s =>
      s.gpr = s₀.gpr ∧ s.rd = s₀.rd ∧ s.wr = s₀.wr ∧ s.sp = s₀.sp ∧
      s.mem = writeBytes s₀.mem (s₀.gpr .x10) (bytesAt s₀.mem (s₀.gpr .x9) 64) := by
  apply WP.block_append
  refine WP.mono (loads_ok (Or.inl rfl) hin) fun a ha => ?_
  refine WP.mono (stores_ok a .x10 (by intro j hj; rw [ha.wr,ha.gpr]; exact hout j hj)) fun s hs => ?_
  refine ⟨hs.gpr.trans ha.gpr,hs.rd.trans ha.rd,hs.wr.trans ha.wr,hs.sp.trans ha.sp,?_⟩
  rw [hs.mem,ha.mem,ha.gpr]
  have eq (j : Nat) (hj : j < 4) : a.v (vr j) = s₀.mem.readW (s₀.gpr .x9 + BitVec.ofNat 64 (16*j)) 128 := by
    simpa only [Nat.zero_add] using ha.loaded j hj hj
  simp only [writeQ4]
  rw [eq 0 (by omega_using []),eq 1 (by omega_using []),eq 2 (by omega_using []),eq 3 (by omega_using [])]
  exact writeQ4_copy _ _ _ _

structure Xored (s₀ s : State) : Prop where
  gpr : s.gpr = s₀.gpr
  mem : s.mem = s₀.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  words : ∀ j < 4, s.v (vr j) = s₀.v (vr j) ^^^ s₀.v (vr (4+j))

theorem xors_ok (s₀ : State) :
    WP isa (.block VG.Impl.Scrypt.AArch64.Transfer.xors) s₀ (Xored s₀) := by
  change WP isa (.block [.vop (.logic .eor (vr 0) (vr 0) (vr 4)),
    .vop (.logic .eor (vr 1) (vr 1) (vr 5)),.vop (.logic .eor (vr 2) (vr 2) (vr 6)),
    .vop (.logic .eor (vr 3) (vr 3) (vr 7))]) s₀ _
  refine WP.block_cons_iff.mpr ⟨_,exec_xorQ,?_⟩
  refine WP.block_cons_iff.mpr ⟨_,exec_xorQ,?_⟩
  refine WP.block_cons_iff.mpr ⟨_,exec_xorQ,?_⟩
  refine WP.block_cons_iff.mpr ⟨_,exec_xorQ,?_⟩
  refine WP.block_nil ⟨rfl,rfl,rfl,rfl,rfl,?_⟩
  intro j hj
  obtain rfl | rfl | rfl | rfl : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by omega_using [hj]
  all_goals rfl

theorem writeQ4_xor (m m' : Mem) (d a b : Addr) :
    writeQ4 m d (fun j => m'.readW (a + BitVec.ofNat 64 (16*j)) 128 ^^^
      m'.readW (b + BitVec.ofNat 64 (16*j)) 128) =
      writeBytes m d (VG.Spec.Pbkdf2.xorBytes (bytesAt m' a 64) (bytesAt m' b 64)) := by
  simp only [writeQ4,Nat.reduceMul,BitVec.add_zero]
  rw [writeW_xor 16 m m' d a b,
    writeW_xor 16 _ m' (d + BitVec.ofNat 64 16) (a + BitVec.ofNat 64 16) (b + BitVec.ofNat 64 16),
    writeW_xor 16 _ m' (d + BitVec.ofNat 64 32) (a + BitVec.ofNat 64 32) (b + BitVec.ofNat 64 32),
    writeW_xor 16 _ m' (d + BitVec.ofNat 64 48) (a + BitVec.ofNat 64 48) (b + BitVec.ofNat 64 48)]
  have join (n : Nat) (hn : n ≤ 48) :
      writeBytes (writeBytes m d (VG.Spec.Pbkdf2.xorBytes (bytesAt m' a n) (bytesAt m' b n)))
        (d + BitVec.ofNat 64 n)
        (VG.Spec.Pbkdf2.xorBytes (bytesAt m' (a + BitVec.ofNat 64 n) 16)
          (bytesAt m' (b + BitVec.ofNat 64 n) 16)) =
      writeBytes m d (VG.Spec.Pbkdf2.xorBytes (bytesAt m' a (n+16)) (bytesAt m' b (n+16))) := by
    rw [VG.Proof.Scrypt.Memory.bytesAt_add,VG.Proof.Scrypt.Memory.bytesAt_add,
      VG.Spec.Pbkdf2.xorBytes,VG.Spec.Pbkdf2.xorBytes,VG.Spec.Pbkdf2.xorBytes,
      List.zipWith_append (by simp [bytesAt])]
    simpa only [VG.Spec.Pbkdf2.xorBytes,List.length_zipWith,VG.Proof.Scrypt.Memory.bytesAt_length,Nat.min_self] using
      VG.Proof.Sha256.Stream.writeBytes_append m d
        (VG.Spec.Pbkdf2.xorBytes (bytesAt m' a n) (bytesAt m' b n))
        (VG.Spec.Pbkdf2.xorBytes (bytesAt m' (a + BitVec.ofNat 64 n) 16)
          (bytesAt m' (b + BitVec.ofNat 64 n) 16)) (by simp [VG.Spec.Pbkdf2.xorBytes,bytesAt]; omega_using [hn])
  rw [join 16 (by omega_using []),join 32 (by omega_using []),join 48 (by omega_using [])]

theorem xorPacket_ok (s₀ : State)
    (hinx : ∀ j < 4, InRegions (s₀.rd ++ s₀.wr) (s₀.gpr .x9 + BitVec.ofNat 64 (16*j)) 16)
    (hiny : ∀ j < 4, InRegions (s₀.rd ++ s₀.wr) (s₀.gpr .x10 + BitVec.ofNat 64 (16*j)) 16)
    (hout : ∀ j < 4, InRegions s₀.wr (s₀.gpr .x11 + BitVec.ofNat 64 (16*j)) 16) :
    WP isa (.block VG.Impl.Scrypt.AArch64.Transfer.xorPacket) s₀ fun s =>
      s.gpr = s₀.gpr ∧ s.rd = s₀.rd ∧ s.wr = s₀.wr ∧ s.sp = s₀.sp ∧
      s.mem = writeBytes s₀.mem (s₀.gpr .x11)
        (VG.Spec.Pbkdf2.xorBytes (bytesAt s₀.mem (s₀.gpr .x9) 64) (bytesAt s₀.mem (s₀.gpr .x10) 64)) := by
  apply WP.block_append
  apply WP.block_append
  apply WP.block_append
  refine WP.mono (loads_ok (Or.inl rfl) hinx) fun a ha => ?_
  refine WP.mono (loads_ok (b := .x10) (Or.inr rfl)
    (by intro j hj; rw [ha.rd,ha.wr,ha.gpr]; exact hiny j hj)) fun b hb => ?_
  refine WP.mono (xors_ok b) fun c hc => ?_
  refine WP.mono (stores_ok c .x11
    (by intro j hj; rw [hc.wr,hb.wr,ha.wr,hc.gpr,hb.gpr,ha.gpr]; exact hout j hj)) fun s hs => ?_
  refine ⟨hs.gpr.trans (hc.gpr.trans (hb.gpr.trans ha.gpr)),
    hs.rd.trans (hc.rd.trans (hb.rd.trans ha.rd)),hs.wr.trans (hc.wr.trans (hb.wr.trans ha.wr)),
    hs.sp.trans (hc.sp.trans (hb.sp.trans ha.sp)),?_⟩
  rw [hs.mem,hc.mem,hb.mem,ha.mem,hc.gpr,hb.gpr,ha.gpr]
  have vals (j : Nat) (hj : j < 4) : c.v (vr j) =
      s₀.mem.readW (s₀.gpr .x9 + BitVec.ofNat 64 (16*j)) 128 ^^^
        s₀.mem.readW (s₀.gpr .x10 + BitVec.ofNat 64 (16*j)) 128 := by
    rw [hc.words j hj,hb.keep (vr j) (by intro k hk; exact vr_ne (by omega_using [hj]) (by omega_using [hk]) (by omega_using [hj]))]
    have he : a.v (vr j) = s₀.mem.readW (s₀.gpr .x9 + BitVec.ofNat 64 (16*j)) 128 := by
      simpa only [Nat.zero_add] using ha.loaded j hj hj
    rw [he,hb.loaded j hj hj,ha.mem,ha.gpr]
  simp only [writeQ4]
  rw [vals 0 (by omega_using []),vals 1 (by omega_using []),vals 2 (by omega_using []),vals 3 (by omega_using [])]
  exact writeQ4_xor _ _ _ _ _

end VG.Proof.Scrypt.AArch64.Transfer

end

end


@[expose] public section
namespace VG.Proof.Scrypt.AArch64.RoMix
open VG VG.AArch64
open VG.Spec.Scrypt (bytesAt)
open VG.Spec.Pbkdf2 (xorBytes)
open VG.Proof.Sha256.Stream (writeBytes writeBytes_nil)
open VG.Proof.MdStream.AArch64 (wp_addImm wp_subImm eval_nonzero ofNat_beq_zero ofNat_pred)
open VG.Proof.Scrypt.Memory (toNat_ofNat_lt add_ofNat)
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
    rw [e,BitVec.toNat_add,toNat_ofNat_lt (by omega_using [hj])]
    exact Nat.mod_le _ _
  simp only [Region.Contains] at hc ⊢
  omega_using [hj, hc, le]

theorem next_packet (p : Addr) (k : Nat) :
    p + BitVec.ofNat 64 (64*k) + BitVec.ofNat 64 64 = p + BitVec.ofNat 64 (64*(k+1)) := by
  rw [add_ofNat,Nat.mul_succ]

theorem packet_count {n k : Nat} (hk : k < n) :
    BitVec.ofNat 64 (8*(n-k)) - BitVec.ofNat 64 8 = BitVec.ofNat 64 (8*(n-(k+1))) := by
  rw [VG.Proof.MdStream.AArch64.sub_ofNat (by omega_using [hk])]
  congr 1; omega_using []

theorem packet_ne {n k : Nat} (hk : k < n) (hn : 64*n < 2^64) :
    (BitVec.ofNat 64 (8*(n-(k+1))) != 0) = decide (k+1 ≠ n) := by
  rw [bne,ofNat_beq_zero (by omega_using [hn])]
  by_cases h : k+1 = n
  · simp [h]
  · simp [show 8*(n-(k+1)) ≠ 0 by omega_using [hk, h],h]

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
      (hsep.sep (by simp only [Region.Contains,BitVec.sub_self,BitVec.toNat_zero]; omega_using [hk])
        (by simp only [Region.Contains,BitVec.sub_self,BitVec.toNat_zero]; omega_using [hk])) (by omega_using [hlt, hk])
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
