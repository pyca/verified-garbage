module

public import VerifiedGarbage.Proof.AesGcm.AArch64.DirectGather.GenericAlignedCT
import VerifiedGarbage.Proof.AesGcm.AArch64.Gather.LoopCT
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.AesGcm.AArch64.DirectGather.BatchesCT
import VerifiedGarbage.Proof.AesGcm.AArch64.Env
import VerifiedGarbage.Proof.Framework.AArch64.RelCT
meta import VerifiedGarbage.Proof.AesGcm.AArch64.RelBase
meta import VerifiedGarbage.Proof.AesGcm.AArch64.DirectGather.GenericLoop

/-! Public descriptor values determine both the encryption and hash cursors.
The nonce-derived counter and processed data may differ between calls. -/

@[expose] public section
namespace VG.Proof.AesGcm.AArch64.DirectGather.Generic

open VG VG.AArch64
open VG.Proof.Gcm.AArch64.Stitch (BatchIn PendingIn batchTest)
abbrev TextArgs.withIcb (a : TextArgs) (iv : Spec.Gcm.Block) := { a with icb := iv }

abbrev PublicDesc (a : TextArgs) (s t : State) :=
  ∀ d < a.count*16, s.mem (atOff a.src d) = t.mem (atOff a.src d)

variable {a : TextArgs} {s t u w : State} {iv : Spec.Gcm.Block} {i j h : Nat}
structure Shared (a : TextArgs) (s t : State) (iv : Spec.Gcm.Block) (i : Nat) : Prop where
  gl : a.gl s i = (a.withIcb iv).gl t i
  srcEq : frag a s i = frag (a.withIcb iv) t i
  lenEq : len a s i = len (a.withIcb iv) t i

theorem Shared.of_public (d : PublicDesc a s t) (hi : i < a.count) : Shared a s t iv i :=
  ⟨Gather.gl_agree d (Nat.le_of_lt hi),Gather.sb_agree d hi,Gather.sl_agree d hi⟩

theorem hashCount_eq (stitch : Bool) (d : PublicDesc a s t) (hi : i ≤ a.count) :
    hashCount stitch a s i = hashCount stitch (a.withIcb iv) t i := by
  induction i with
  | zero => rfl
  | succ i ih =>
    have pub : Shared a s t iv i := Shared.of_public d (by omega_arith)
    rw [hashCount,hashCount,pub.gl,pub.lenEq,ih (by omega_arith)]

theorem Shared.input (d : Shared a s t iv i) (p : PieceAt (a.withIcb iv) t i j h w)
    (pr : PiecesPre (a.withIcb iv) t) (hi : i < a.count) :
    CrInG a.Wn true a.Ctx a.St a.W a.SP w.gpr a.R (pos a s i j) (atOff (frag a s i) j)
      (atOff a.dst (pos a s i j)) (len a s i-j) w := by
  simpa only [pos,← d.lenEq,← d.srcEq,← d.gl,TextArgs.withIcb] using p.inputs pr hi

theorem PieceAt.batchIn (p : PieceAt a s i j h u) (pr : PiecesPre a s) (hi : i < a.count) :
    BatchIn a.Wn a.Ctx a.St a.W a.SP (atOff (frag a s i) j) (atOff a.dst (pos a s i j)) a.R (len a s i-j) u := by
  have inc := p.inputs pr hi
  obtain ⟨hw,apart,_⟩ := inc.outAt
  exact ⟨p.env,pr.rounds,p.x22,p.src,p.rest,p.dst,inc.data,hw,apart⟩

theorem PieceAt.pending (p : PieceAt a s i j h u) (pr : PiecesPre a s) (hi : i < a.count)
    (whole : len a s i-j=0 ∨ pos a s i j%16=0) (nz : batchTest (len a s i-j) ≠ 0) :
    PendingIn a.Wn a.St a.W (atOff a.dst (16*h)) (atOff a.dst (pos a s i j)) (pos a s i j/16-h) u := by
  have nonzero : len a s i-j ≠ 0 := fun e => nz (by rw [e]; decide)
  have al := whole.resolve_left nonzero
  have upper := pieceBound a s hi
  have le := p.le
  have endP : pos a s i j ≤ a.total s := by dsimp [pos]; omega_arith
  have hb := p.hashBound
  refine ⟨p.hashPtr,?_,?_⟩
  · simp only [atOff,Offset.add_add]; congr 2; omega_arith
  · exact (((pr.dst.ok.drop (by omega_arith : 16*h ≤ a.total s)).take
      (by omega_arith : 16*(pos a s i j/16-h) ≤ a.total s-16*h)).of_eq p.rd p.wr)

theorem PieceAt.tail_rel (v : GcmImpl) (d : Shared a s t iv i) (p : PieceAt a s i j h u)
    (q : PieceAt (a.withIcb iv) t i j h w) (pa : PiecesPre a s) (pb : PiecesPre (a.withIcb iv) t) (hi : i < a.count)
    (whole : len a s i-j=0 ∨ pos a s i j%16=0) (hv : v.ctr.scratch ≤ a.Wn-512) :
    RelCT isa (Eq2 u w) (.ite (.zero .x .x24) (.block []) (Impl.AesGcm.AArch64.DirectGather.aligned v.callees)) TT := by
  have c := d.input q pb hi
  have l := (pa.source i hi).lt
  change len a s i < 2^64 at l
  refine rel_ite (eval_zero p.rest (by omega_arith)) (eval_zero c.x24 (by omega_arith))
    (fun _ => rel_taint [] (p.env.sp.trans q.env.sp.symm) (by agree_tac []) ⟨.block [] 256,by decide⟩) (fun e => ?_)
  exact aligned_rel pa.lay v (p.inputs pa hi) c (whole.resolve_left (of_decide_eq_false e)) hv

end VG.Proof.AesGcm.AArch64.DirectGather.Generic

/-! Relate the generic gather loops with identical public descriptors. The
contents of the slices, key, and nonce-derived counter may all differ. -/

@[expose] public section
namespace VG.Proof.AesGcm.AArch64.DirectGather.Generic

open VG VG.AArch64 VG.Impl.AesGcm.AArch64
open VG.Impl.AesGcm.AArch64.DirectGather (pieces batches)
open VG.Proof.Gcm.AArch64.Stitch (BatchIn PendingIn batchTest GatherLaws)
variable {a : TextArgs} {s t u w : State} {iv : Spec.Gcm.Block} {i j h : Nat}

theorem pieceBatch_rel (v : GcmImpl) (stitch : Bool) (gh : stitch = true → GatherLaws)
    (d : Shared a s t iv i) (p : PieceAt a s i j h u) (q : PieceAt (a.withIcb iv) t i j h w)
    (pa : PiecesPre a s) (pb : PiecesPre (a.withIcb iv) t) (hi : i < a.count)
    (whole : len a s i-j=0 ∨ pos a s i j%16=0) :
    RelCT isa (Eq2 u w) (if stitch then batches v.callees else .block []) TT := by
  cases stitch
  · simp only [Bool.false_eq_true,ite_false]; exact rel_taint [] (p.env.sp.trans q.env.sp.symm) (by agree_tac []) ⟨.block [] 256,by decide⟩
  have whole₂ : len (a.withIcb iv) t i-j=0 ∨ pos (a.withIcb iv) t i j%16=0 := by
    simpa only [pos,← d.gl,← d.lenEq] using whole
  refine batches_rel v (p.batchIn pa hi) ?_ pa.lay (gh rfl) (p.pending pa hi whole) ?_
  · simpa only [pos,← d.gl,← d.srcEq,← d.lenEq,TextArgs.withIcb] using q.batchIn pb hi
  · simpa only [pos,← d.gl,← d.lenEq,TextArgs.withIcb] using q.pending pb hi whole₂

theorem body_trace (v : GcmImpl) (stitch : Bool) (gh : stitch=true → GatherLaws)
    (pa : PiecesPre a s) (pb : PiecesPre (a.withIcb iv) t) (hi : i < a.count) (d : Shared a s t iv i)
    (p : TextAt a s i h u) (q : TextAt (a.withIcb iv) t i h w) (hv : v.ctr.scratch ≤ a.Wn-512) :
    RelCT isa (Eq2 u w) (body v stitch) TT := by
  refine rel_seq (rel_taint [.x27] (p.env.sp.trans q.env.sp.symm) (by agree_tac [p.desc,q.desc,TextArgs.withIcb])
    ⟨_,by taint_decide⟩) (decode_ok p pa hi) (decode_ok q pb hi) fun _ _ x y => ?_
  refine rel_seq (head_rel (x.inputs pa hi) (d.input y pb hi)) (x.head_exact pa hi) (y.head_exact pb hi)
    fun _ _ ⟨f,whole⟩ ⟨g,_⟩ => ?_
  have dp (j : Nat) : pos (a.withIcb iv) t i j = pos a s i j := by rw [pos,pos,d.gl]
  rw [dp,← d.lenEq] at g
  refine rel_seq (pieceBatch_rel v stitch gh d f g pa pb hi whole) (f.batch_exact v stitch pa hi whole gh)
    (g.batch_exact v stitch pb hi (by simpa only [← d.lenEq,dp] using whole) gh) fun _ _ ⟨x',z⟩ ⟨y',_⟩ => ?_
  rw [dp,← d.lenEq] at y'
  refine rel_seq (x'.tail_rel v d y' pa pb hi z hv) (x'.tail v pa hi z hv) (y'.tail v pb hi (by simpa only [← d.lenEq,dp] using z) hv)
    fun _ _ c e => rel_taint [] (c.env.sp.trans e.env.sp.symm) (by agree_tac []) ⟨.block [] 256,by decide⟩

/-- Every loop and batch takes the same branches and accesses the same
addresses for equal public arguments and descriptor bytes. -/
theorem pieces_rel (v : GcmImpl) (stitch : Bool) (pa : PiecesPre a s) (pb : PiecesPre (a.withIcb iv) t)
    (d : PublicDesc a s t) (hv : v.ctr.scratch ≤ a.Wn-512) (gh : stitch=true → GatherLaws) :
    RelCT isa (Eq2 s t) (pieces v.callees stitch) TT := by
  have lt := pa.descLt
  have count₂ : t.gpr .x28 = BitVec.ofNat 64 a.count := pb.x28
  refine rel_ite (eval_zero pa.x28 (by omega_arith)) (eval_zero count₂ (by omega_arith))
    (fun _ => rel_taint [] (pa.env.sp.trans pb.env.sp.symm) (by agree_tac []) ⟨.block [] 256,by decide⟩)
    (fun nz => ?_)
  have nonzero := of_decide_eq_false nz
  refine (RelCT.loop (Q := TT) (fun n u w => ∃ i h, n = a.count-i ∧ i < a.count ∧
      TextAt a s i h u ∧ TextAt (a.withIcb iv) t i h w)
      (fun n => ?_) a.count).mono (fun u w ⟨eu,ew⟩ => by subst u w; exact ⟨0,0,rfl,by omega_arith,TextAt.start pa,TextAt.start pb⟩)
      fun _ _ h => h
  refine RelCT.exists_ fun i => RelCT.exists_ fun h => ?_
  by_cases cond : n = a.count-i ∧ i < a.count
  · obtain ⟨rfl,hi⟩ := cond
    have shared : Shared a s t iv i := Shared.of_public d hi
    let nh := nextHash stitch (a.gl s i) (len a s i) h
    have rel : RelCT isa (fun u w => TextAt a s i h u ∧ TextAt (a.withIcb iv) t i h w) (body v stitch)
        (fun u w => TextAt a s (i+1) nh u ∧ TextAt (a.withIcb iv) t (i+1) nh w) := by
      have tr : RelCT isa (fun u w => TextAt a s i h u ∧ TextAt (a.withIcb iv) t i h w) (body v stitch) TT :=
        fun u w x y z₁ z₂ ⟨p,q⟩ => body_trace v stitch gh pa pb hi shared p q hv _ _ x y z₁ z₂ ⟨rfl,rfl⟩
      exact (tr.wp fun u w ⟨p,q⟩ => ⟨body_exact v stitch pa hi p hv gh,
        by simpa only [nh,← shared.gl,← shared.lenEq] using body_exact v stitch pb hi q hv gh⟩).mono
        (fun _ _ x => x) fun _ _ x => x.2
    refine rel.mono (fun _ _ x => x.2.2) ?_
    rintro u w ⟨p,q⟩
    have e₁ := eval_nonzero p.count (by omega_arith)
    have c₂ : w.gpr .x28 = BitVec.ofNat 64 (a.count-(i+1)) := q.count
    have e₂ := eval_nonzero c₂ (by omega_arith)
    refine ⟨by rw [e₁,e₂],fun _ => trivial,fun yes => ?_⟩
    rw [e₁] at yes
    have nxt : i+1 < a.count := by simp at yes; omega_arith
    exact ⟨a.count-(i+1),by omega_arith,i+1,nh,rfl,nxt,p,q⟩
  · exact RelCT.of_false fun _ _ z => cond ⟨z.1,z.2.1⟩

end VG.Proof.AesGcm.AArch64.DirectGather.Generic
