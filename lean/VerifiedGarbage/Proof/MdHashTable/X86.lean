module

public import VerifiedGarbage.Impl.MdHashTable.X86
public import VerifiedGarbage.Proof.Pbkdf2.Md.X86.Block
public import VerifiedGarbage.Proof.Framework.X86.RelCT
public import VerifiedGarbage.Proof.Framework.X86.CallWith
import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.Framework.X86.Call

/-!
# The digest of a hash value on x86 (32-bit)

`digestK H`: the contract of `digest out` (`Impl/MdHashTable/X86.lean`) for
a hash function `H` whose streaming code's digest code is `out`: with the
`N` bytes of the hash value at `ebx` readable and the `N` bytes at `eax`
writable, apart, and apart from the return address, it writes `H.digest` of
the hash value to `eax` (`digest_ok`, from what `OutOk` says of `out`), in
constant time for the same pointers (`digest_ct`, from the taint check of
`out`). Its call through a table, in the frame that pushes `ebx`, from a
state with the pointers as `DigArgs` says: `dig_frame` and `dig_rel`.
-/

@[expose] public section

namespace VG.Proof.MdHashTable.X86

open VG VG.X86
open VG.Impl.MdHashTable.X86 (digest)
open VG.Proof.MdStream (Md)

variable {B N L : Nat} (H : Md B N L)

/-- The contract of `digest(value = ebx, out = eax)`. -/
def digestK : Contract isa where
  pre s :=
    let value : Region := ⟨(s.gpr .ebx).setWidth 64, N⟩
    let out : Region := ⟨(s.gpr .eax).setWidth 64, N⟩
    let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
    s.rd = [value] ∧ s.wr = [out] ∧ value.Disjoint out ∧ ret.Disjoint out ∧ (s.gpr .ebx).toNat + N ≤ 2 ^ 32 ∧
      (s.gpr .eax).toNat + N ≤ 2 ^ 32
  post s s' := s'.mem =
    WriteBytes.writeBytes s.mem ((s.gpr .eax).setWidth 64) (H.digest (H.stateAt s.mem ((s.gpr .ebx).setWidth 64)))
  pub s₁ s₂ := s₁.gpr .esp = s₂.gpr .esp ∧ s₁.gpr .ebx = s₂.gpr .ebx ∧ s₁.gpr .eax = s₂.gpr .eax

variable {H}

/-- `digest out` meets `digestK H`. -/
theorem digest_ok {out : List Instr} (ho : Proof.Pbkdf2.Md.X86.OutOk H out) :
    ∀ s, (digestK H).pre s → ∃ t s', Exec isa (digest out) s t s' ∧ abiPreserved s s' ∧ (digestK H).post s s' := by
  intro s ⟨hrd, hwr, hvo, hro, hb, ha⟩
  have hw := ho s hb ha (by rw [hrd]; exact ⟨_, List.mem_append_left _ (List.mem_singleton_self _),
      Region.contains_self _ _⟩) (by rw [hwr]; exact ⟨_, List.mem_singleton_self _, Region.contains_self _ _⟩) hvo
  obtain ⟨t, s', he, hg, -, -, hm⟩ := hw
  refine ⟨t, s', he, ⟨fun r hr => hg r ?_ ?_, ?_⟩, hm⟩
  · rintro rfl; simp [calleeSaved] at hr
  · rintro rfl; simp [calleeSaved] at hr
  · have hl : (H.digest (H.stateAt s.mem ((s.gpr .ebx).setWidth 64))).length = N := H.digest_length _
    rw [hm]
    exact (WriteBytes.writeBytes_frame s.mem ((s.gpr .eax).setWidth 64) _ (R := ⟨(s.gpr .eax).setWidth 64, N⟩)
      (by rw [hl]; exact Region.contains_self _ _)).readW (r := ⟨(s.gpr .esp).setWidth 64, 32 / 8⟩)
      (Region.contains_self _ _) (fun r hr => by rw [List.mem_singleton.mp hr]; exact hro) (by decide)

/-- `digest out` is constant time for the same pointers. -/
theorem digest_ct {out : List Instr}
    (hc : ∃ hc, (VG.Taint.check VG.X86.taint (τr [.esp, .ebx, .eax]) (digest out) hc).isSome = true) :
    ConstantTime isa (digestK H).pre (digestK H).pub (digest out) := by
  obtain ⟨_, hc⟩ := hc
  intro s₁ s₂ t₁ t₂ s₁' s₂' _ _ hp e₁ e₂
  refine (RelCT.taint (A := VG.X86.taint) (P := fun a b => (digestK H).pub a b) (τr [.esp, .ebx, .eax])
    (fun a b h => agree_regs fun r hr => ?_) hc s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂).1
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  obtain ⟨h1, h2, h3⟩ := h
  rcases hr with rfl | rfl | rfl <;> assumption


/-! ## The call, in a frame pushing `ebx` -/

open VG.Proof.Pbkdf2.Stream.X86 (stk After after_of stk_sub covers_one)

/-- What the call of the digest needs of the state before its push: the
hash value at `v` in `ebx`, readable, and the digest's place at `o` in `eax`,
writable, apart, and apart from the 48 bytes below `esp`, none wrapping
around. -/
structure DigArgs (N : Nat) (s : State) (v o : BitVec 32) : Prop where
  ebx : s.gpr .ebx = v
  eax : s.gpr .eax = o
  sp48 : 48 ≤ (s.gpr .esp).toNat
  cv : Covers [⟨v.setWidth 64, N⟩] (s.rd ++ s.wr)
  co : Covers [⟨o.setWidth 64, N⟩] s.wr
  vo : Region.Disjoint ⟨v.setWidth 64, N⟩ ⟨o.setWidth 64, N⟩
  b_v : (stk s).Disjoint ⟨v.setWidth 64, N⟩
  b_o : (stk s).Disjoint ⟨o.setWidth 64, N⟩
  nv : v.toNat + N ≤ 2 ^ 32
  no : o.toNat + N ≤ 2 ^ 32

namespace DigArgs

variable {N : Nat} {s : State} {v o : BitVec 32} (h : DigArgs N s v o)
include h

theorem fit : 4 * [Reg.ebx].length + 4 ≤ (s.gpr .esp).toNat := by
  have := h.sp48; simp only [List.length_cons, List.length_nil]; omega

theorem callPre {B L : Nat} (H : Md B N L) :
    CallPre (digestK H) [.ebx] [⟨v.setWidth 64, N⟩] [⟨o.setWidth 64, N⟩] s := by
  have e := h.sp48
  refine ⟨?_, ?_, ?_⟩
  · simp only [digestK, State.withRegions_rd, State.withRegions_wr, State.withRegions_gpr,
      callEntry_gpr' _ _ (show Reg.ebx ≠ .esp by decide), callEntry_gpr' _ _ (show Reg.eax ≠ .esp by decide), h.ebx, h.eax,
      callEntry_esp']
    have sR : Region.Sub ⟨(s.gpr .esp - BitVec.ofNat 32 8).setWidth 64, 4⟩ (stk s) :=
      stk_sub e (by omega) (by omega)
    exact ⟨trivial, trivial, h.vo, h.b_o.sub_left sR, h.nv, h.no⟩
  · intro a n ⟨q, hq, hc⟩
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · obtain ⟨q', hq', hc'⟩ := h.cv a n ⟨_, List.mem_singleton_self _, hc⟩
      rcases List.mem_append.mp hq' with hq' | hq'
      · exact ⟨q', List.mem_append_left _ hq', hc'⟩
      · exact ⟨q', List.mem_append_right _ (List.mem_cons_of_mem _ hq'), hc'⟩
    · obtain ⟨q', hq', hc'⟩ := h.co a n ⟨_, List.mem_singleton_self _, hc⟩
      exact ⟨q', List.mem_append_right _ (List.mem_cons_of_mem _ hq'), hc'⟩
  · intro a n hi
    obtain ⟨q', hq', hc'⟩ := h.co a n hi
    exact ⟨q', List.mem_cons_of_mem _ hq', hc'⟩

theorem entry_frame : Frame [stk s] s.mem (pushed [.ebx] s).callEntry.mem :=
  (callEntry_frame h.fit (by decide)).sub fun q hq => by
    simp only [List.mem_singleton] at hq; subst hq
    exact ⟨_, List.mem_singleton_self _, below_sub (by simp only [List.length_cons, List.length_nil]; omega) h.sp48⟩

end DigArgs

variable {out : List Instr} {n : String}

/-- The call of the digest in the frame pushing `ebx`: the `N` bytes at `o`
are the digest of the hash value at `v`, and only they and the stack below
`esp` are written. -/
theorem dig_frame (ho : Proof.Pbkdf2.Md.X86.OutOk H out) (hsp : NoSp (digest out)) {s : State} {v o : BitVec 32}
    (h : DigArgs N s v o) {Q : State → Prop}
    (hQ : ∀ s', After s [⟨o.setWidth 64, N⟩] s' →
      (∀ i < N, s'.mem (o.setWidth 64 + BitVec.ofNat 64 i) =
        (H.digest (H.stateAt s.mem (v.setWidth 64))).getD i 0) → Q s') :
    WP isa (.frame (.push [.ebx]) (.call n (digest out)) (.pop .eax [Reg.ebx].length)) s Q := by
  have e := h.sp48
  refine WP.callWith (digest_ok ho) hsp (by simp) (by decide)
    (by simp only [List.length_cons, List.length_nil, digest, stackUse]; omega) (h.callPre H)
    fun s' rd' wr' cs' f' ⟨s₂, m₂, post⟩ => ?_
  have f'' : Frame ([⟨o.setWidth 64, N⟩] ++ [below (s.gpr .esp) 8]) s.mem s'.mem := by
    simpa [digest, stackUse] using f'
  refine hQ s' (after_of e (by decide) rd' wr' cs' f'') fun i hi => ?_
  have post' : s₂.mem = VG.WriteBytes.writeBytes (pushed [.ebx] s).callEntry.mem
      (((pushed [.ebx] s).callEntry.gpr .eax).setWidth 64)
      (H.digest (H.stateAt (pushed [.ebx] s).callEntry.mem (((pushed [.ebx] s).callEntry.gpr .ebx).setWidth 64))) :=
    post
  rw [callEntry_gpr' _ _ (show Reg.ebx ≠ .esp by decide), callEntry_gpr' _ _ (show Reg.eax ≠ .esp by decide), h.ebx,
    h.eax] at post'
  have hl : (H.digest (H.stateAt (pushed [.ebx] s).callEntry.mem (v.setWidth 64))).length = N := H.digest_length _
  have e₁ : H.stateAt (pushed [.ebx] s).callEntry.mem (v.setWidth 64) = H.stateAt s.mem (v.setWidth 64) :=
    H.stateAt_congr fun j hj => h.entry_frame.bytes (R := ⟨v.setWidth 64, N⟩)
      (by simp only [List.mem_singleton]; rintro q rfl; exact h.b_v.symm)
      (by show N ≤ 2 ^ 64; have := h.nv; omega) hj
  have hi' : (BitVec.ofNat 64 i).toNat = i := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := h.no; omega)]
  rw [← m₂, post', ← e₁]
  simp only [VG.WriteBytes.writeBytes]
  rw [BitVec.add_comm, BitVec.add_sub_cancel, hi', hl, ite_eq_left hi]

/-- Two runs of the call of the digest, from the same pointers and `esp`. -/
theorem dig_rel (ho : Proof.Pbkdf2.Md.X86.OutOk H out)
    (hc : ∃ hc, (VG.Taint.check VG.X86.taint (τr [.esp, .ebx, .eax]) (digest out) hc).isSome = true)
    {P : State → State → Prop} {sp v o : BitVec 32}
    (h : ∀ s s', P s s' → DigArgs N s v o ∧ DigArgs N s' v o ∧ s.gpr .esp = sp ∧ s'.gpr .esp = sp) :
    RelCT isa P (.frame (.push [.ebx]) (.call n (digest out)) (.pop .eax [Reg.ebx].length)) fun _ _ => True := by
  refine RelCT.callWith (digest_ok ho) (digest_ct hc) [⟨v.setWidth 64, N⟩] [⟨o.setWidth 64, N⟩] fun s s' hp => ?_
  obtain ⟨a, a', e, e'⟩ := h s s' hp
  refine ⟨a.callPre H, a'.callPre H, e.trans e'.symm, ?_, ?_, ?_⟩
  · simp only [State.withRegions_gpr, callEntry_esp', e, e']
  · simp only [State.withRegions_gpr, callEntry_gpr' _ _ (show Reg.ebx ≠ .esp by decide), a.ebx, a'.ebx]
  · simp only [State.withRegions_gpr, callEntry_gpr' _ _ (show Reg.eax ≠ .esp by decide), a.eax, a'.eax]

end VG.Proof.MdHashTable.X86
