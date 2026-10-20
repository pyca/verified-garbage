module
public import VerifiedGarbage.Impl.Dsa.X86.Generation.Hash
public import VerifiedGarbage.Proof.Dsa.X86.Generation.HashResources
import VerifiedGarbage.Proof.Dsa.X86.Generation.HashArguments

/-! # Fixed-width seed hashing uses the existing verified streaming contracts -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Proof.Mont.X86
open VG.Impl.Pbkdf2.Stream.X86 (Hash)
open VG.Proof.Pbkdf2.Stream.X86
open VG.Impl.Dsa.X86.Generation

theorem hash_after_keeps {s t : State} {ws : List Region} (A : After s ws t) :
    Keeps [.eax, .ebx, .ecx, .edx] s t := by
  refine ⟨fun r hr => A.cs r ?_, A.rd, A.wr⟩
  cases r <;> simp_all [calleeSaved]

theorem hash_frame_mono {rs ws : List Region} {m m' : Mem} (F : Frame rs m m') (h : rs ⊆ ws) :
    Frame ws m m' := F.sub fun r hr => ⟨r, h hr, fun _ hi => hi⟩

theorem hash_input_frame {H : Hash} {K : HashOK H} {input output scratch : BitVec 32} {len : Nat}
    {s : State} {m : Mem} (R : HashResources K input output scratch len s)
    (F : Frame [⟨(scratch + 512#32).setWidth 64, H.S⟩, ⟨scratch.setWidth 64, K.Wb⟩, stk s] s.mem m) :
    Spec.Sha256.bytesAt m (input.setWidth 64) len = Spec.Sha256.bytesAt s.mem (input.setWidth 64) len := by
  unfold Spec.Sha256.bytesAt
  apply List.map_congr_left
  intro i hi
  refine F.bytes (R := ⟨input.setWidth 64, len⟩) ?_ (by show len ≤ 2 ^ 64; have := R.lenBound; omega) (List.mem_range.mp hi)
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  exacts [R.inputState, R.inputScratch, R.stackInput.symm]

theorem seedHash_ok {H : Hash} (K : HashOK H) {s : State} {input output scratch : BitVec 32} (len : Nat)
    (R : HashResources K input output scratch len s)
    (si : s.gpr .esi = input) (di : s.gpr .edi = output) (bp : s.gpr .ebp = scratch) :
    WP isa (seedHash H len) s fun t =>
      (Spec.Sha256.bytesAt t.mem (output.setWidth 64) H.F).take H.D =
        K.SH.H.hash (Spec.Sha256.bytesAt s.mem (input.setWidth 64) len) ∧
      Frame [⟨(scratch + 512#32).setWidth 64, H.S⟩, ⟨output.setWidth 64, H.F⟩,
        ⟨scratch.setWidth 64, K.Wb⟩, stk s] s.mem t.mem ∧
      Keeps [.eax, .ebx, .ecx, .edx] s t := by
  unfold seedHash
  refine WP.seq (WP.mono hashHead_ok fun a ⟨bx, ma, ka⟩ => ?_)
  have Ra := R.keeps ka (by decide)
  rw [bp] at bx
  refine WP.seq (init_frame K (Ra.init bx) fun b ab reprB => ?_)
  have Rb := Ra.after ab
  have kb := (ka.mono (by decide)).trans (hash_after_keeps ab)
  have bxB : b.gpr .ebx = scratch + 512#32 := (ab.cs .ebx (by decide)).trans bx
  have fB : Frame [⟨(scratch + 512#32).setWidth 64, H.S⟩, ⟨scratch.setWidth 64, K.Wb⟩, stk s] s.mem b.mem := by
    have F := ab.frame
    rw [ma, show stk a = stk s from congrArg (fun sp => below sp 48) (ka.1 _ (by decide))] at F
    refine hash_frame_mono F ?_
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, List.cons_append, List.nil_append] at hr ⊢
    rcases hr with h | h
    · exact .inl h
    · exact .inr (.inr h)
  refine WP.seq (WP.mono (hashUpdateArgs_ok len) fun c ⟨dx, cx, ax, mc, kc⟩ => ?_)
  have Rc := Rb.keeps kc (by decide)
  have bxC : c.gpr .ebx = scratch + 512#32 := (kc.1 _ (by decide)).trans bxB
  have bpC : c.gpr .ebp = scratch := (kc.1 _ (by decide)).trans ((kb.1 _ (by decide)).trans bp)
  rw [kb.1 _ (by decide), si] at dx
  refine WP.seq (upd_frame K (Rc.update bxC ax cx dx bpC) fun d cd reprD => ?_)
  have Rd := Rc.after cd
  have kd := ((kb.trans (kc.mono (by decide))).trans (hash_after_keeps cd))
  have reprC : K.SH.Repr c.mem ((scratch + 512#32).setWidth 64) [] := by rw [mc]; exact reprB
  have reprD' := reprD [] reprC (by decide)
  simp only [List.nil_append] at reprD'
  have bytesC : Spec.Sha256.bytesAt c.mem (input.setWidth 64) len = Spec.Sha256.bytesAt s.mem (input.setWidth 64) len := by
    rw [mc]; exact hash_input_frame R fB
  rw [bytesC] at reprD'
  have bxD : d.gpr .ebx = scratch + 512#32 := (cd.cs .ebx (by decide)).trans bxC
  have fD : Frame [⟨(scratch + 512#32).setWidth 64, H.S⟩, ⟨scratch.setWidth 64, K.Wb⟩, stk s] s.mem d.mem := by
    have F := cd.frame
    rw [mc, show stk c = stk s from congrArg (fun sp => below sp 48) ((kc.1 _ (by decide)).trans (kb.1 _ (by decide)))] at F
    exact fB.trans F
  refine WP.seq (WP.mono (hashFinalizeArgs_ok len) fun e ⟨dxE, axE, cxE, me, ke⟩ => ?_)
  have Re := Rd.keeps ke (by decide)
  have bxE : e.gpr .ebx = scratch + 512#32 := (ke.1 _ (by decide)).trans bxD
  have bpE : e.gpr .ebp = scratch := (ke.1 _ (by decide)).trans ((kd.1 _ (by decide)).trans bp)
  rw [kd.1 _ (by decide), di] at dxE
  refine fin_frame K (Re.finalize bxE axE cxE dxE bpE) fun t et result => ?_
  have reprE : K.SH.Repr e.mem ((scratch + 512#32).setWidth 64)
      (Spec.Sha256.bytesAt s.mem (input.setWidth 64) len) := by rw [me]; exact reprD'
  have lenEq : (Spec.Sha256.bytesAt s.mem (input.setWidth 64) len).length = len := by
    simp only [Spec.Sha256.bytesAt, List.length_map, List.length_range]
  refine ⟨result _ reprE (by rw [lenEq]; have := R.lenBound; omega) ?_, ?_,
    (kd.trans (ke.mono (by decide))).trans (hash_after_keeps et)⟩
  · rw [lenEq]
    exact zero_append_ofNat R.lenBound
  · have F := et.frame
    rw [me, show stk e = stk s from congrArg (fun sp => below sp 48) ((ke.1 _ (by decide)).trans (kd.1 _ (by decide)))] at F
    refine (hash_frame_mono fD ?_).trans F
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
    rcases hr with h | h | h
    · exact .inl h
    · exact .inr (.inr (.inl h))
    · exact .inr (.inr (.inr h))
end VG.Proof.Dsa.X86.Generation
