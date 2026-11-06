module

public import VerifiedGarbage.Proof.RsaKeyGen.X86_64.Generate.KeyCall
public import VerifiedGarbage.Proof.RsaKeyGen.X86_64.Key.Verified
import VerifiedGarbage.Proof.Bignum.Layout
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset

/-! # The key, run

`keyRun`: in a frame of its stack arguments, the key's arguments and its
call. It leaves the key's status and its outputs at the key's buffer, and
writes nothing else but the working space and the stack.
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.X86_64.Generate

open VG.Proof.RsaKeyGen.SearchFrame

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.Ffdh.X86_64.Generation (allocated allocated_rsp allocated_reg allocated_mem freed freed_rsp
  freed_reg freed_mem frame_alloc)
open VG.Impl.RsaKeyGen.X86_64.Generate
open VG.Spec.RsaKeyGen

/-- The key, as the controller calls it. -/
def keyCall : Prog isa := .call "vg_rsa_keygen_key" VG.Impl.RsaKeyGen.X86_64.Key.code

theorem keyCode_mx : VG.Impl.RsaKeyGen.X86_64.Key.code.allInstrs (fun i => !loadsMxcsr i) = true := by
  decide +kernel

theorem keyCode_noSp : NoSp VG.Impl.RsaKeyGen.X86_64.Key.code := by
  have h : VG.Impl.RsaKeyGen.X86_64.Key.code.allInstrs (fun i => !Taint.clobbers i .rsp) = true := by
    decide +kernel
  intro i hi
  rw [Code.allInstrs_eq] at h
  simpa using List.all_eq_true.mp h i hi

theorem keyCode_depth : Code.depth VG.Impl.RsaKeyGen.X86_64.Key.code = 0 := by decide +kernel

/-- The key from the primes at the slots of `p` and `q`. -/
abbrev keyOf (p : GenPublic) (m : Mem) : Except Failure (List (List Byte)) ⊕ Unit :=
  keyOp p.L p.eB (Spec.Rsa.bytesAt m (p.slot 4) p.L) (Spec.Rsa.bytesAt m (p.slot 5) p.L)

/-- The key's outputs at the key's buffer. -/
def keyOutsOf (p : GenPublic) : List (Addr × Nat) :=
  [(p.kp, 2 * p.L), (p.slot 2, 2 * p.L), (p.slot 4, p.L), (p.slot 5, p.L), (p.slot 6, p.L), (p.slot 7, p.L),
    (p.slot 8, p.L)]

/-- What the key leaves. -/
structure AfterKey (p : GenPublic) (original : State) (used : Nat) (st : KeyProgress) (s t : State) : Prop where
  frame : GenFrame p original used st t
  status : ((t.gpr .rax).setWidth 32).toNat = keyStatus (keyOf p s.mem)
  out : match keyOf p s.mem with
    | .inl (.ok ys) => (keyOutsOf p).map (fun o => Spec.Rsa.bytesAt t.mem o.1 o.2) = ys
    | _ => ∀ o ∈ keyOutsOf p, Spec.Rsa.bytesAt t.mem o.1 o.2 = List.replicate o.2 0
  mem : Frame [cK p, rS p, ⟨p.sp - BitVec.ofNat 64 552, 392⟩] s.mem t.mem

section

variable {p : GenPublic} {original s : State} {used : Nat} {st : KeyProgress}

theorem key_covers_writes (h : GenFrame p original used st s) {u : State}
    (hw : u.wr = (allocated 96 s).wr) : Covers (kWrites p) u.wr := by
  have hf := h.input.cfacts
  have hk := h.key_region
  have hs : inScr original = rS p := by rw [← h.input.2]; rfl
  have hwo : original.wr = [inKey original, inUsed original, inScr original, inState original] :=
    h.input.1.2.2.2.1
  rw [hk, hs] at hwo
  rw [hw]
  have hin : ∀ q ∈ [(⟨p.kp, 9 * p.L⟩ : Region), rS p], q ∈ (allocated 96 s).wr := by
    intro q hq
    show q ∈ _ :: s.wr
    rw [h.wr, hwo]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq ⊢
    rcases hq with rfl | rfl <;> simp
  obtain ⟨hL1, -, -⟩ := hf.len
  refine Covers.of_sub fun r hr => ?_
  simp only [kWrites, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨⟨p.kp, 9 * p.L⟩, hin _ (by simp), 0, by simp, by simp; omega⟩
  · exact ⟨⟨p.kp, 9 * p.L⟩, hin _ (by simp), 2 * p.L, rfl, by simp; omega⟩
  · exact ⟨⟨p.kp, 9 * p.L⟩, hin _ (by simp), 4 * p.L, rfl, by simp; omega⟩
  · exact ⟨⟨p.kp, 9 * p.L⟩, hin _ (by simp), 5 * p.L, rfl, by simp; omega⟩
  · exact ⟨⟨p.kp, 9 * p.L⟩, hin _ (by simp), 6 * p.L, rfl, by simp; omega⟩
  · exact ⟨⟨p.kp, 9 * p.L⟩, hin _ (by simp), 7 * p.L, rfl, by simp; omega⟩
  · exact ⟨⟨p.kp, 9 * p.L⟩, hin _ (by simp), 8 * p.L, rfl, by simp; omega⟩
  · exact ⟨rS p, hin _ (by simp), 0, by simp, by simp⟩

theorem key_covers_reads (h : GenFrame p original used st s) {u : State}
    (hrd : u.rd = (allocated 96 s).rd) (hw : u.wr = (allocated 96 s).wr) :
    Covers (kReads p ++ kWrites p) (u.rd ++ u.wr) := by
  refine Covers.append_left ?_ (key_covers_writes h hw).right
  have ht : inState original = cS p := by rw [← h.input.2]; rfl
  have hwo : original.wr = [inKey original, inUsed original, inScr original, inState original] :=
    h.input.1.2.2.2.1
  rw [ht] at hwo
  rw [hrd, hw]
  refine Covers.of_sub fun r hr' => ?_
  simp only [kReads, List.mem_cons, List.not_mem_nil, or_false] at hr'
  rcases hr' with rfl | rfl
  · refine ⟨cS p, List.mem_append_right _ ?_, 48, rfl, by simp⟩
    show cS p ∈ _ :: s.wr
    rw [h.wr, hwo]; simp
  · refine ⟨⟨s.gpr .rsp - BitVec.ofNat 64 96, 96⟩, List.mem_append_right _ (List.mem_cons_self ..), 0, ?_, by simp⟩
    rw [h.rsp, F_96, BitVec.add_zero]

theorem key_frame_sub (h : GenFrame p original used st s) :
    ∀ r ∈ [cK p, rS p, (⟨p.sp - BitVec.ofNat 64 552, 392⟩ : Region)],
      ∃ q ∈ GenInput.callChanges original, Region.Sub r q := by
  have hk := h.key_region
  have hs : inScr original = rS p := by rw [← h.input.2]; rfl
  have hS : (⟨original.gpr .rsp - BitVec.ofNat 64 stackUse, 392⟩ : Region) =
      ⟨p.sp - BitVec.ofNat 64 552, 392⟩ := by rw [← h.input.2]; rfl
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  simp only [GenInput.callChanges, hk, hs, hS]
  rcases hr with rfl | rfl | rfl <;> exact ⟨_, by simp, fun _ h => h⟩

end

theorem key_run {p : GenPublic} {original s : State} {used : Nat} {st : KeyProgress}
    (h : GenFrame p original used st s) :
    WP isa (keyRun keyCall) s (AfterKey p original used st s) := by
  have hf := h.input.cfacts
  have hF := h.input.F_toNat
  have hroom := h.input.room
  unfold keyRun keyCall
  apply frame_alloc (by decide) (by decide) (by decide) (by rw [h.rsp, hF]; have : 552 ≤ p.sp.toNat := hroom; omega)
  refine WP.seq (WP.mono (key_args_ok h) fun u ⟨ha, hm, k⟩ => ?_)
  have hu : u.gpr .rsp = p.sp - BitVec.ofNat 64 256 := by
    rw [k.gpr (by decide), allocated_rsp, h.rsp, F_96]
  refine WP.call_mx (k := Key.keyCtr) (Key.keyCode_correct keyCode_mx) keyCode_noSp
    (by rw [keyCode_depth]; decide) (callK_pre h hu ha hm) (key_covers_reads h k.2.1 k.2.2)
    (key_covers_writes h k.2.2) fun t htr htw hg hfr _ ⟨s₂, hm₂, hg₂, hpost⟩ _ => ?_
  obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11⟩ := callK_args (s := s) hu hm
  obtain ⟨hdi, hsi, hdx, hcx, h8, h9⟩ := ha
  obtain ⟨hL1, hL2, hL3⟩ := hf.len
  have tl : (BitVec.ofNat 64 p.L).toNat = p.L := toNat_ofNat_lt (by omega)
  have t2 : (BitVec.ofNat 64 (2 * p.L)).toNat = 2 * p.L := toNat_ofNat_lt (by omega)
  have hcf := callK_frame (s := s) hu hm
  have hst := hf.stack
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hst
  obtain ⟨sK, -, -, sT, -⟩ := hst
  have hbytes {R : Region} (hR : Region.Sub R (cK p) ∨ Region.Sub R (cS p)) (hn : R.len ≤ 2 ^ 64) :
      Spec.Rsa.bytesAt (callK p u).mem R.base R.len = Spec.Rsa.bytesAt s.mem R.base R.len := by
    simp only [Spec.Rsa.bytesAt]
    refine List.map_congr_left fun i hi => ?_
    refine hcf.bytes (fun r hr => ?_) hn (List.mem_range.mp hi)
    obtain rfl := List.mem_singleton.mp hr
    rcases hR with hR | hR
    exacts [sK.sub_left hR, sT.sub_left hR]
  have hres : Key.keyRes (callK p u) = keyOf p s.mem := by
    simp only [Key.keyRes, Key.arg, callK_gpr (show Reg.r8 ≠ .rsp by decide),
      callK_gpr (show Reg.r9 ≠ .rsp by decide), h8, h9, tl]
    rw [show stackArg (callK p u) 8 = _ from a8, show stackArg (callK p u) 9 = _ from a9,
      show stackArg (callK p u) 0 = _ from a0, toNat_ofNat_lt (show 8 < 2 ^ 64 by decide)]
    rw [hbytes (R := ⟨p.stp + BitVec.ofNat 64 48, 8⟩) (.inr rE_sub) (by show 8 ≤ 2 ^ 64; decide),
      hbytes (R := ⟨p.slot 4, p.L⟩) (.inl (kSlot_sub (by omega))) (by show p.L ≤ 2 ^ 64; omega),
      hbytes (R := ⟨p.slot 5, p.L⟩) (.inl (kSlot_sub (by omega))) (by show p.L ≤ 2 ^ 64; omega)]
    have he : Spec.Rsa.bytesAt s.mem (p.stp + BitVec.ofNat 64 48) 8 = p.eB := h.state.e
    rw [he]
  have houts : Key.keyOuts (callK p u) = keyOutsOf p := by
    simp only [Key.keyOuts, Key.arg, callK_gpr (show Reg.rdi ≠ .rsp by decide),
      callK_gpr (show Reg.rsi ≠ .rsp by decide), callK_gpr (show Reg.rdx ≠ .rsp by decide),
      callK_gpr (show Reg.r8 ≠ .rsp by decide), callK_gpr (show Reg.r9 ≠ .rsp by decide), hdi, hsi, hdx, h8,
      h9, tl, t2]
    rw [show stackArg (callK p u) 0 = _ from a0, show stackArg (callK p u) 2 = _ from a2,
      show stackArg (callK p u) 4 = _ from a4, show stackArg (callK p u) 6 = _ from a6]
    rfl
  obtain ⟨hstat, hout⟩ := hpost
  rw [hres] at hstat hout
  rw [houts] at hout
  -- The memory: the stack arguments, then the key.
  have mK : cK p ∈ [cK p, rS p, (⟨p.sp - BitVec.ofNat 64 552, 392⟩ : Region)] := List.mem_cons_self ..
  have mS : rS p ∈ [cK p, rS p, (⟨p.sp - BitVec.ofNat 64 552, 392⟩ : Region)] :=
    List.mem_cons_of_mem _ (List.mem_cons_self ..)
  have mT : (⟨p.sp - BitVec.ofNat 64 552, 392⟩ : Region) ∈ [cK p, rS p, (⟨p.sp - BitVec.ofNat 64 552, 392⟩ : Region)] :=
    List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))
  have f₀ : Frame [cK p, rS p, ⟨p.sp - BitVec.ofNat 64 552, 392⟩] s.mem u.mem := by
    rw [hm, F_96]
    apply (Search.writeFrame_frame_size _ _ (keyValues p) (size := 96) (by decide) (keyValues_bound p)).sub
    intro r hr
    obtain rfl := List.mem_singleton.mp hr
    exact ⟨_, mT, Offset.sub_below _ (by decide) (by decide)⟩
  have hbelow : Region.Sub (below (p.sp - BitVec.ofNat 64 256) 8) ⟨p.sp - BitVec.ofNat 64 552, 392⟩ := by
    simp only [below, BitVec.sub_sub]
    rw [← BitVec.ofNat_add]
    exact Offset.sub_below _ (by decide) (by decide)
  have f₁ : Frame [cK p, rS p, ⟨p.sp - BitVec.ofNat 64 552, 392⟩] u.mem t.mem := by
    refine hfr.sub fun r hr => ?_
    rcases List.mem_append.mp hr with hr | hr
    · simp only [kWrites, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact ⟨cK p, mK, kN_sub⟩
      · exact ⟨cK p, mK, kSlot_sub (by omega)⟩
      · exact ⟨cK p, mK, kSlot_sub (by omega)⟩
      · exact ⟨cK p, mK, kSlot_sub (by omega)⟩
      · exact ⟨cK p, mK, kSlot_sub (by omega)⟩
      · exact ⟨cK p, mK, kSlot_sub (by omega)⟩
      · exact ⟨cK p, mK, kSlot_sub (by omega)⟩
      · exact ⟨rS p, mS, fun _ h => h⟩
    · obtain rfl := List.mem_singleton.mp hr
      refine ⟨_, mT, ?_⟩
      rw [hu, keyCode_depth]
      exact hbelow
  have hframe := f₀.trans f₁
  have hword (d : Nat) (hd : d + 8 ≤ 56) : word t.mem p.stp d = word s.mem p.stp d := by
    refine hframe.readW (r := cS p) (Offset.contains_base _ hd (by have := hf.nT; omega)) (fun q hq => ?_)
      (by decide)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact hf.kT.symm
    · exact hf.sT.symm
    · exact sT.sub_right (Region.sub_prefix (by decide))
  have htsp : t.gpr .rsp = (allocated 96 s).gpr .rsp := by rw [hg _ (by decide), k.gpr (by decide)]
  refine ⟨htsp, htw.trans k.2.2, h.restore (htr.trans k.2.1) (show t.wr.tail = s.wr by rw [htw, k.2.2]; rfl)
      (fun r hr => ?_) (hframe.sub (key_frame_sub h)) ((hword 0 (by decide)).trans h.state.remaining)
      ((hword 8 (by decide)).trans h.state.len) ((hword 16 (by decide)).trans h.state.cap) (.inl rfl) rfl
      h.state.remaining_le, ?_, ?_, hframe⟩
  · have hnot : r ∉ [Reg.rax, .rdi, .rsi, .rdx, .rcx, .r8, .r9] := by revert r; decide
    by_cases he : r = .rsp
    · subst he
      rw [freed_rsp, htsp, allocated_rsp]
      exact BitVec.sub_add_cancel _ _
    · rw [freed_reg _ _ _ he, hg r hr, k.gpr hnot, allocated_reg _ _ _ he]
  · rw [freed_reg _ _ _ (by decide), ← hg₂ _ (by decide)]; exact hstat
  · rw [freed_mem, ← hm₂]; exact hout

end VG.Proof.RsaKeyGen.X86_64.Generate
