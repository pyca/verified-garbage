import VerifiedGarbage.Proof.AesGcm.X86_64.StreamTo.Base
import VerifiedGarbage.Proof.AesGcm.X86_64.Callee
import VerifiedGarbage.Proof.Gcm.StreamTo

/-!
# AES-GCM streaming encryption out of place, x86-64: between the calls

Untrusted: everything here is checked by Lean. With `o` bytes done, the
state and the output are those of the text so far followed by the first
`o` bytes of the plaintext (`Sem`), and the arguments are kept with the
memory changed only where the code may write (`Mid`); after the entry,
`Mid s 0` (`mid_entry`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86_64.StreamTo

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcm.X86_64
open VG.Proof.Gcm.X86_64.Stitch (CtxMode)
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt StreamRepr ctxCiph ctxH gctr inc32 j0)

section
variable (s : State)

/-- The rounds. -/
abbrev R : Nat := (s.gpr .rsi).toNat
/-- The cipher and the hash subkey of the key context. -/
abbrev ciph : Block → Block := ctxCiph s.mem (K s) (R s)
abbrev hk : Block := ctxH s.mem (K s)
/-- The first `o` bytes of the plaintext. -/
abbrev pt (o : Nat) : List Byte := bytesAt s.mem (Src s) o

end

/-- With `o` bytes done, in memory `m`: the state represents the text so far
followed by the first `o` bytes of the plaintext, and the output holds
their encryption. -/
def Sem (s : State) (o : Nat) (m : Mem) : Prop :=
  ∀ iv a p, StreamRepr s.mem (St s) (ciph s) (hk s) iv a (gctr (ciph s) (inc32 (j0 (hk s) iv)) p) →
    AL s = BitVec.ofNat 64 a.length → (TL s).toNat = p.length →
    StreamRepr m (St s) (ciph s) (hk s) iv a (gctr (ciph s) (inc32 (j0 (hk s) iv)) (p ++ pt s o)) ∧
      bytesAt m (Dst s) o = (gctr (ciph s) (inc32 (j0 (hk s) iv)) (p ++ pt s o)).drop p.length

/-- `o` bytes done, in state `st`. -/
structure Mid (s : State) (o : Nat) (st : State) : Prop where
  o_le : o ≤ L s
  tl : (TL s).toNat + o < 2 ^ 64
  rsp : st.gpr .rsp = SP s
  saved : ∀ r ∈ calleeSaved, st.gpr r = s.gpr r
  rd : st.rd = s.rd
  wr : st.wr = s.wr
  kept : Kept s o st.mem
  frame : Frame (wR s ++ [tR s]) s.mem st.mem
  sem : Sem s o st.mem

/-- `Mid` through code that changes no memory, `rsp` or callee-saved register. -/
theorem Mid.regs {s : State} {o : Nat} {st st' : State} (h : Mid s o st) (hm : st'.mem = st.mem)
    (hcs : ∀ r ∈ calleeSaved, st'.gpr r = st.gpr r) (hrd : st'.rd = st.rd) (hwr : st'.wr = st.wr) :
    Mid s o st' :=
  ⟨h.o_le, h.tl, by rw [hcs _ (by decide), h.rsp], fun r hr => by rw [hcs r hr, h.saved r hr],
    hrd.trans h.rd, hwr.trans h.wr, hm ▸ h.kept, hm ▸ h.frame, hm ▸ h.sem⟩

/-- A streaming state is what it is outside a frame. -/
theorem streamRepr_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr}
    (hd : ∀ r ∈ rs, (⟨p, 80⟩ : Region).Disjoint r) {ciph : Block → Block} {h : Block}
    {iv a c : List Byte} (hr : StreamRepr m p ciph h iv a c) : StreamRepr m' p ciph h iv a c := by
  have sub : ∀ {d k : Nat}, d + k ≤ 80 → ∀ r ∈ rs, (⟨p + BitVec.ofNat 64 d, k⟩ : Region).Disjoint r :=
    fun hk r hr => (hd r hr).sub_left (Offset.sub_base _ hk)
  have e : ∀ d : Nat, p + (OfNat.ofNat d : Addr) = p + BitVec.ofNat 64 d := fun _ => rfl
  rw [Proof.Gcm.streamRepr_iff, e, e, e] at hr ⊢
  obtain ⟨hj, ha, hc⟩ := hr
  have e0 := blockAt_frame hf (sub (d := 0) (k := 16) (by decide))
  simp only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] at e0
  refine ⟨by rw [e0, hj], ha.congr (blockAt_frame hf (sub (by decide)))
    (bytesAt_frame hf (sub (d := 32) (k := (Spec.Gcm.ghashInput a c).length % 16) (by omega)) (by omega)),
    hc.congr (blockAt_frame hf (sub (by decide))) (blockAt_frame hf (sub (by decide)))⟩

section
variable {M : CtxMode} {s : State} (hp : SP' M s)
include hp

/-- The key context, outside a frame of the regions written and the stack. -/
theorem k_disj : ∀ r ∈ wR s ++ [tR s], (kR M s).Disjoint r := by
  intro r hr
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with (rfl | rfl | rfl) | rfl
  exacts [hp.k_st, hp.k_d, hp.k_w, hp.b_k.symm]

/-- The plaintext, outside a frame of the regions written and the stack. -/
theorem r_disj : ∀ r ∈ wR s ++ [tR s], (srcR s).Disjoint r := by
  intro r hr
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with (rfl | rfl | rfl) | rfl
  exacts [hp.st_r.symm, hp.r_d, hp.r_w, hp.b_r.symm]

/-- The cipher, through a frame of the regions written and the stack. -/
theorem ciph_eq {m : Mem} (hf : Frame (wR s ++ [tR s]) s.mem m) : ctxCiph m (K s) (R s) = ciph s := by
  have hRb : 16 * (R s + 1) ≤ 256 := by rcases hp.rounds with h | h | h <;> simp only [R, h] <;> decide
  simp only [ciph, ctxCiph]
  rw [bytesAt_frame hf (fun r hr => (k_disj hp r hr).sub_left (Region.sub_prefix (Nat.le_trans hRb M.ge)))
    (by have := hp.w_k; have := M.ge; omega)]

/-- The hash subkey, through a frame of the regions written and the stack. -/
theorem hk_eq {m : Mem} (hf : Frame (wR s ++ [tR s]) s.mem m) : ctxH m (K s) = hk s := by
  simp only [hk, ctxH]
  exact blockAt_frame hf fun r hr => (k_disj hp r hr).sub_left (Offset.sub_base _ (by have := M.ge; omega))

/-- The plaintext, through a frame of the regions written and the stack. -/
theorem pt_eq {m : Mem} (hf : Frame (wR s ++ [tR s]) s.mem m) {o : Nat} (ho : o ≤ L s) :
    bytesAt m (Src s) o = pt s o :=
  bytesAt_frame hf (fun r hr => (r_disj hp r hr).sub_left (Region.sub_prefix ho))
    (by have : L s < 2 ^ 64 := (stackArg s 0).isLt; omega)

omit hp in
theorem Kept.frame {o : Nat} {m m' : Mem} (h : Kept s o m) {rs : List Region} (hf : Frame rs m m')
    (hd : ∀ r ∈ rs, (kR' s).Disjoint r) : Kept s o m' := by
  have k : ∀ d, d + 8 ≤ 72 → m'.readW (W s + BitVec.ofNat 64 d) 64 = m.readW (W s + BitVec.ofNat 64 d) 64 :=
    fun d hd' => hf.readW (Offset.contains_base _ hd' (by omega)) hd (by decide)
  have k0 : m'.readW (W s) 64 = m.readW (W s) 64 := by simpa using k 0 (by decide)
  exact ⟨by rw [k0]; exact h.ctx, by rw [k 8 (by decide)]; exact h.rounds, by rw [k 16 (by decide)]; exact h.st,
    by rw [k 24 (by decide)]; exact h.aad, by rw [k 32 (by decide)]; exact h.tl,
    by rw [k 40 (by decide)]; exact h.src, by rw [k 48 (by decide)]; exact h.len,
    by rw [k 56 (by decide)]; exact h.dst, by rw [k 64 (by decide)]; exact h.done⟩

omit hp in
/-- A frame of the slots kept is one of the regions written. -/
theorem frame_kR' {m m' : Mem} (hf : Frame [kR' s] m m') : Frame (wR s ++ [tR s]) m m' :=
  hf.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨wkR s, by simp, kR'_sub⟩

/-- After the entry: nothing done. -/
theorem mid_entry {s₁ : State} (hsp : s₁.gpr .rsp = s.gpr .rsp)
    (hcs : ∀ r ∈ calleeSaved, s₁.gpr r = s.gpr r)
    (hk : Kept s 0 s₁.mem) (hf : Frame [kR' s] s.mem s₁.mem) (hrd : s₁.rd = s.rd) (hwr : s₁.wr = s.wr) :
    Mid s 0 s₁ := by
  refine ⟨Nat.zero_le _, by have := (TL s).isLt; omega, hsp, hcs, hrd, hwr, hk, frame_kR' hf,
    fun iv a p hr _ hl => ⟨?_, ?_⟩⟩
  all_goals have z : pt s 0 = [] := rfl
  · rw [z, List.append_nil]
    exact streamRepr_frame hf (fun r hr' => by
      simp only [List.mem_singleton] at hr'; subst hr'
      exact hp.st_w.sub_right kR'_sub) hr
  · rw [z, List.append_nil, List.drop_eq_nil_of_le (by rw [Proof.Gcm.length_gctr])]
    rfl

end

end VG.Proof.AesGcm.X86_64.StreamTo
