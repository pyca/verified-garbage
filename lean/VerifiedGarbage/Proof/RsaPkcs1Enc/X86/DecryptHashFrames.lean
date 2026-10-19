module

public import VerifiedGarbage.Proof.RsaPkcs1Enc.X86.DecryptDArgs
public import VerifiedGarbage.Proof.RsaPkcs1Enc.X86.DecryptPrivateCall
public import VerifiedGarbage.Proof.Sha256.Scratch

/-! # Hash calls preserve the encoded message and the saved private-RSA status -/

@[expose] public section
namespace VG.Proof.RsaPkcs1Enc.X86.Dec
open VG VG.X86 VG.Proof.Bignum.X86 VG.Proof.Mont.X86
open VG.Impl.RsaPkcs1Enc.X86.Decrypt

def hashWrites (g : Geometry) : List Region :=
  [g.workspaceRegion, g.calleeRegion, ⟨byteAddr g.stack, 80⟩]

theorem hashWrites_body {g : Geometry} {bs : Fin 9 → List Byte} {s : State} (h : Context g bs s) :
    ∀ r ∈ hashWrites g, ∃ R ∈ bodyWrites g, r.Sub R := by
  intro r hr
  simp only [hashWrites, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact ⟨_, by simp [bodyWrites], fun _ hx => hx⟩
  · exact ⟨_, by simp [bodyWrites], fun _ hx => hx⟩
  · exact ⟨g.innerRegion, by simp [bodyWrites], h.outgoingSub⟩

theorem hash_output {g : Geometry} {bs : Fin 9 → List Byte} {s t : State}
    (h : Context g bs s) (F : Frame (hashWrites g) s.mem t.mem) :
    Spec.Rsa.bytesAt t.mem (byteAddr g.output) g.length = Spec.Rsa.bytesAt s.mem (byteAddr g.output) g.length := by
  apply VG.Proof.Rsa.rsa_bytes_frame F (by have := h.valid.maxLength; omega)
  intro r hr
  simp only [hashWrites, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact h.valid.outputWorkspace
  · exact (h.valid.stackOutput.sub_left h.valid.calleeSub).symm
  · exact (h.valid.stackOutput.sub_left (fun x hx => h.valid.innerSub x (h.outgoingSub x hx))).symm

theorem hash_status {g : Geometry} {bs : Fin 9 → List Byte} {s t : State}
    (h : Context g bs s) (F : Frame (hashWrites g) s.mem t.mem) : savedStatus g t = savedStatus g s := by
  have slot : (⟨byteAddr g.stack + BitVec.ofNat 64 oR, 4⟩ : Region).Sub g.innerRegion :=
    Offset.sub_base _ (by decide)
  apply F.readW (r := ⟨byteAddr g.stack + BitVec.ofNat 64 oR, 4⟩) (Region.contains_self _ _) ?_ (by decide)
  intro r hr
  simp only [hashWrites, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact h.valid.stackWorkspace.sub_left (fun x hx => h.valid.innerSub x (slot x hx))
  · exact (h.valid.calleeInner.sub_right slot).symm
  · exact Offset.disjoint_base _ (by decide : 80 ≤ oR) (by decide)

theorem hash_call_ok {g : Geometry} {bs : Fin 9 → List Byte} {s : State}
    (h : Context g bs s) {name : String} {code : Prog isa} {contract : Contract isa}
    (verified : Verified target code contract) (stack : stackUse code ≤ 3368) (noSp : NoSp code)
    {rd wr : List Region} (pre : contract.pre (s.callEntry.withRegions rd wr))
    (read : Covers (rd ++ wr) (s.rd ++ s.wr)) (write : Covers wr s.wr)
    (sub : ∀ r ∈ wr, ∃ R ∈ hashWrites g, r.Sub R) :
    WP isa (.call name code) s fun t => Context g bs t ∧
      Frame (hashWrites g) s.mem t.mem ∧ Frame (wr ++ [g.calleeRegion]) s.mem t.mem ∧
      Keeps callClobbers s t ∧
      ∃ u : State, u.mem = t.mem ∧ (∀ r, r ≠ .esp → u.gpr r = t.gpr r) ∧
        contract.post (s.callEntry.withRegions rd wr) u := by
  have bodySub : ∀ r ∈ wr, ∃ R ∈ bodyWrites g, r.Sub R := by
    intro r hr
    obtain ⟨mid, member, sm⟩ := sub r hr
    obtain ⟨last, lastMem, sl⟩ := hashWrites_body h mid member
    exact ⟨last, lastMem, fun x hx => sl x (sm x hx)⟩
  refine WP.mono (private_call_ok h verified stack noSp pre read write bodySub) ?_
  rintro t ⟨ht, F, K, post⟩
  refine ⟨ht, F.sub ?_, F, K, post⟩
  intro r hr
  rcases List.mem_append.mp hr with hr | hr
  · exact sub r hr
  · obtain rfl := List.mem_singleton.mp hr
    exact ⟨g.calleeRegion, by simp [hashWrites], fun _ hx => hx⟩

theorem repr_frame {m m' : Mem} {rs : List Region} {p : Addr} {iv : Spec.Sha256.HashValue} {msg : List Byte}
    (F : Frame rs m m') (separate : ∀ r ∈ rs, (⟨p, 96⟩ : Region).Disjoint r)
    (repr : Spec.Sha256.ReprFrom iv m p msg) : Spec.Sha256.ReprFrom iv m' p msg :=
  VG.Proof.Sha256.reprFrom_congr
    (fun i hi => F.bytes separate (by decide : 96 ≤ 2 ^ 64) hi) repr

end VG.Proof.RsaPkcs1Enc.X86.Dec
