import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.CachedHashCall

namespace VG.Proof.MlDsa.AArch64.Sign.Cached
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Call (callAt sc)
open VG.Impl.MlDsa.AArch64.Sign
open VG.Impl.MlDsa.AArch64.Sign.Cached (hashArgs)

theorem hashCall_tr {p : Params} {S : Nat} {n : String} {c : Prog isa} {k : Contract isa} (C : CalleeOk S c k)
    {P : State → State → Prop}
    (hP : ∀ x y x1 y1, P x y → Args (hashArgs p) x x1 → Args (hashArgs p) y y1 → ∃ rd wr : List Region,
      k.pre (x1.callEntry.withRegions rd wr) ∧ k.pre (y1.callEntry.withRegions rd wr) ∧
      k.pub (x1.callEntry.withRegions rd wr) (y1.callEntry.withRegions rd wr) ∧
      Covers (rd ++ wr) (x.rd ++ x.wr) ∧ Covers wr x.wr ∧
      Covers (rd ++ wr) (y.rd ++ y.wr) ∧ Covers wr y.wr) :
    RelCT isa P (callAt n c (hashArgs p)) fun _ _ => True :=
  RelCT.seq (RelCT.postDep (Q := fun x1 y1 => ∃ x y, P x y ∧ Args (hashArgs p) x x1 ∧ Args (hashArgs p) y y1)
      (block_nomem_tr (glue_nomem (hashArgs p))) (fun x y _ => ⟨hashGlue_ok p x, hashGlue_ok p y⟩)
      fun x y _ _ hp h1 h2 => ⟨x, y, hp, h1, h2⟩)
    (RelCT.mono (RelCT.exists_ (P := fun (a : List Region × List Region) (x1 y1 : State) =>
        k.pre (x1.callEntry.withRegions a.1 a.2) ∧ k.pre (y1.callEntry.withRegions a.1 a.2) ∧
        k.pub (x1.callEntry.withRegions a.1 a.2) (y1.callEntry.withRegions a.1 a.2) ∧
        Covers (a.1 ++ a.2) (x1.rd ++ x1.wr) ∧ Covers a.2 x1.wr ∧
        Covers (a.1 ++ a.2) (y1.rd ++ y1.wr) ∧ Covers a.2 y1.wr)
      fun a => RelCT.call C.correct C.ct a.1 a.2 fun _ _ h => h)
      (fun x1 y1 ⟨x, y, hp, h1, h2⟩ => by
        obtain ⟨rd, wr, p₁, p₂, pub, c₁, w₁, c₂, w₂⟩ := hP x y x1 y1 hp h1 h2
        exact ⟨(rd, wr), p₁, p₂, pub, by rw [h1.2.rd, h1.2.wr]; exact c₁, by rw [h1.2.wr]; exact w₁,
          by rw [h2.2.rd, h2.2.wr]; exact c₂, by rw [h2.2.wr]; exact w₂⟩)
      fun _ _ h => h)


theorem hashRegions_eq {p : Params} {x y : State} (e : SameB x y) :
    hashReads p x=hashReads p y ∧ hashWrites p x=hashWrites p y := by
  simp only [hashReads,hashWrites]
  rw [e.pa (p:=(.x26,0)) (by decide),e.pa (p:=sc oW1) (by decide),
    e.pa (p:=sc oMS) (by decide),e.pa (p:=sc oCT) (by decide),
    e.pa (p:=t1P) (by decide),e.pa (p:=t4P) (by decide)]
  exact ⟨rfl,rfl⟩

theorem hashReady_tr {p : Params} (hp : p=mlDsa65 ∨ p=mlDsa87)
    {S : Nat} (hS : S<2^64) {P : State→State→Prop}
    (hP : ∀x y,P x y→Lay S (sgR p) (sgW p) x ∧ Lay S (sgR p) (sgW p) y ∧ SameB x y) :
    RelCT isa P (callAt (if p.ℓ=5 then "vg_mldsa_commit_tail65" else "vg_mldsa_commit_tail87")
      (Impl.MlDsa.AArch64.Sign.CommitTail.code (p.k*w1Len p) (cLen p)) (hashArgs p))
      fun _ _=>True := by
  have C : CalleeOk S (Impl.MlDsa.AArch64.Sign.CommitTail.code (p.k*w1Len p) (cLen p))
      (commitTailContract abi (p.k*w1Len p) (cLen p) S) := by
    rcases hp with rfl|rfl
    · exact CommitTail.callee65 hS
    · exact CommitTail.callee87 hS
  refine hashCall_tr C fun x y x1 y1 hxy hx hy => ?_
  obtain ⟨Lx,Ly,e⟩ := hP x y hxy
  obtain ⟨hr,hw⟩ := hashRegions_eq (p:=p) e
  refine ⟨hashReads p x,hashWrites p x,hash_pre hp Lx hx,?_,?_,
    (hash_cov hp Lx).1,(hash_cov hp Lx).2,?_,?_⟩
  · rw [hr,hw]; exact hash_pre hp Ly hy
  · sig_pub [commitTailContract,commitTailSig,AArch64.abi,AArch64.argRegs]
    rw [hx.ptr (r:=.x0) (p:=(.x26,0)) (by simp [hashArgs]),
      hx.ptr (r:=.x1) (p:=sc oW1) (by simp [hashArgs]),
      hx.ptr (r:=.x2) (p:=sc oCT) (by simp [hashArgs]),
      hx.ptr (r:=.x3) (p:=t1P) (by simp [hashArgs]),
      hx.ptr (r:=.x4) (p:=sc oMS) (by simp [hashArgs]),
      hx.ptr (r:=.x6) (p:=t4P) (by simp [hashArgs]),
      hy.ptr (r:=.x0) (p:=(.x26,0)) (by simp [hashArgs]),
      hy.ptr (r:=.x1) (p:=sc oW1) (by simp [hashArgs]),
      hy.ptr (r:=.x2) (p:=sc oCT) (by simp [hashArgs]),
      hy.ptr (r:=.x3) (p:=t1P) (by simp [hashArgs]),
      hy.ptr (r:=.x4) (p:=sc oMS) (by simp [hashArgs]),
      hy.ptr (r:=.x6) (p:=t4P) (by simp [hashArgs]),Args.sp hx,Args.sp hy]
    exact ⟨e.2,e.pa (by decide),e.pa (by decide),e.pa (by decide),
      e.pa (by decide),e.pa (by decide),e.pa (by decide)⟩
  · rw [hr,hw]; exact (hash_cov hp Ly).1
  · rw [hw]; exact (hash_cov hp Ly).2

end VG.Proof.MlDsa.AArch64.Sign.Cached
