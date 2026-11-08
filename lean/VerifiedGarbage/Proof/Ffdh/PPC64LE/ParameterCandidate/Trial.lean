module

public import VerifiedGarbage.Proof.Ffdh.PPC64LE.ParameterCandidate.Keep
public import VerifiedGarbage.Proof.Ffdh.PPC64LE.ParameterCandidate.Contract
public import VerifiedGarbage.Proof.Ffdh.PPC64LE.ParameterCandidate.MainShape
public import VerifiedGarbage.Proof.RsaKeyGen.PPC64LE.Trial.Loop
public import VerifiedGarbage.Impl.RsaKeyGen.TrialTable32
import VerifiedGarbage.Proof.Bignum.PPC64LE.PreCore
import VerifiedGarbage.Proof.MillerRabin.PPC64LE.Search.Mem
import VerifiedGarbage.Proof.Framework.PPC64LE.Syms
import VerifiedGarbage.Proof.Framework.PPC64LE.Step
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Ffdh.PPC64LE.ParameterCandidate.Tests

-- separate module: its proofs build in parallel with those of `TestsFn`, which `Main` also imports

/-!
# An FFDH parameter candidate on PPC64LE: RSA's table of trial division

`TabIn`: RSA's table of trial division (`VG_RSA_KEYGEN_TRIAL32`) at `T`, its
region readable and apart from the working space, which no piece of the
candidate changes (`TabIn.step`). `MB`: the working space with a value in
array 0 and `hBad` zero exactly when a condition holds; `MB.step`, what
keeps it. The trial division itself is `Product.lean`'s.
-/

@[expose] public section

namespace VG.Proof.Ffdh.PPC64LE.ParameterCandidate

open VG VG.PPC64LE VG.Impl.Bignum VG.Impl.Bignum.PPC64LE VG.Impl.Ffdh.PPC64LE.ParameterCandidate
open VG.Proof.Bignum VG.Proof.Bignum.PPC64LE
open VG.Impl.MillerRabin.PPC64LE.Search VG.Proof.MillerRabin.PPC64LE.Search
open VG.Impl.RsaKeyGen (TrialTable32.symbol TrialTable32.entry)
open VG.Proof.MillerRabin.PPC64LE (Env)

/-- The table at `T`, where the state names it, readable, and apart from
the working space of `Z` bytes at `B`. -/
structure TabIn (B : Addr) (Z : Nat) (T : Addr) (s : State) : Prop where
  sym : s.syms TrialTable32.symbol = T
  tab : TabAt T s.mem
  rd : (⟨T, 8192⟩ : Region) ∈ s.rd
  fit : T.toNat + 8192 ≤ 2 ^ 64
  dj : (⟨T, 8192⟩ : Region).Disjoint ⟨B, Z⟩

/-- The table survives a change of the working space. -/
theorem TabIn.step {B T : Addr} {Z : Nat} {s t : State} {rs : List (Nat × Nat)}
    (h : TabIn B Z T s) (sy : t.syms = s.syms) (hf : Frm B rs s.mem t.mem) (hr : ∀ r ∈ rs, r.1 + r.2 ≤ Z)
    (krd : t.rd = s.rd) : TabIn B Z T t := by
  refine ⟨sy ▸ h.sym, fun i hi => ?_, by rw [krd]; exact h.rd, h.fit, h.dj⟩
  rw [← h.tab i hi]
  refine Mem.readW_congr fun j hj => (hf _ fun r hr' => .inr ?_)
  have hj' : j < 8 := by omega
  have hc : (⟨T, 8192⟩ : Region).Contains (T + BitVec.ofNat 64 (8 * i) + BitVec.ofNat 64 j) 1 := by
    simp only [Region.Contains, BitVec.add_assoc, Offset.add_sub_cancel_left, BitVec.ofNat_add_ofNat,
      BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (by omega)]; omega
  have hn := h.dj _ hc
  simp only [Region.Contains, Nat.not_le] at hn
  have := hr r hr'
  unfold ofs
  omega

/-- The count of entries, `1024 − 512 [bits ≤ 1024]`. -/
theorem trialCount_eq {bits : Nat} (hb : bits ≤ 8192) :
    BitVec.ofNat 64 1024 - (BitVec.ofNat 64 bits - BitVec.ofNat 64 1025) >>> 63 <<< 9 =
      BitVec.ofNat 64 (trialN bits) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_sub, BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat,
    Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow, trialN]
  split <;> omega

/-- In p's working space, with `x` in array 0, `hBad` zero iff `B`, and
the table at `T`. -/
structure MB (p : PP) (T : Addr) (x : Nat) (B : Prop) (t : State) : Prop where
  st : St p t
  ph : Ph p p.bits (Spec.Ffdh.primeChecks p.bits) t
  u : word t.mem p.B 152 = BitVec.ofNat 64 p.L
  n : wv t.mem p.B (slot (wOf p.bits) 0) (wOf p.bits) = x
  bad : word t.mem p.B (8 * hBad) = 0#64 ↔ B
  tab : TabIn p.B p.Z T t

/-- `St.step` without the link register, which `adrSym` writes. -/
theorem St.step' {p : PP} {s t : State} {regs : List Reg} (h : St p s) (hf : Frm p.B (mutR p.n) s.mem t.mem)
    (kg : ∀ r, r ∉ regs → t.gpr r = s.gpr r) (krd : t.rd = s.rd) (kwr : t.wr = s.wr) (ksp : t.sp = s.sp)
    (h31 : Reg.r31 ∉ regs := by decide) (h2 : Reg.r2 ∉ regs := by decide) : St p t where
  scr := h.scr.congr kwr
  r31 := (kg .r31 h31).trans h.r31
  args := h.args.frm hf rfl
  bufs := by
    have hr : ∀ r ∈ mutR p.n, r.1 + r.2 ≤ p.Z := fun r hr => by
      have := h.dims.n
      simp only [mutR, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> dsimp only [PP.Z, saveBytes] <;> omega_arith
    have b := h.bufs
    exact ⟨by rw [krd, kwr]; exact b.rdR, b.sepR, by rw [bytes_frm hf hr b.sepR]; exact b.bR,
      by rw [out_frm hf hr b.sepO (by have := b.scrO.nowrap; omega_arith)]; exact b.bO, b.scrO.congr kwr, b.sepO,
      b.scrU.congr kwr, b.sepU, b.stkR, b.stkO, b.stkU, b.dOU⟩
  dims := h.dims
  ws := by rw [kwr]; exact h.ws
  sp := ksp.trans h.sp
  stk := h.stk
  stkB := h.stkB
  save := fun i hi => by
    have := h.dims.n; have := h.dims.n'; have := h.dims.b1
    refine (hf.word_eq (fun r hr => .inr ?_) (by simp only [saveBytes]; omega_arith)).trans (h.save i hi)
    simp only [mutR, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> dsimp only <;> simp only [saveBytes, PP.L] at * <;> omega_arith
  r2 := (kg .r2 h2).trans h.r2

/-- `MB` survives a change of header words `hBad` and `hTrialN` and of
registers but `r2`, `r10`, `r11`, `r29` and `r31`, with `hBad` then zero iff
`B'`. -/
theorem MB.step {p : PP} {T : Addr} {x : Nat} {B B' : Prop} {s t : State} {regs : List Reg} (h : MB p T x B s)
    (hf : Frm p.B [(208, 8), (200, 8)] s.mem t.mem) (kg : ∀ r, r ∉ regs → t.gpr r = s.gpr r)
    (krd : t.rd = s.rd) (kwr : t.wr = s.wr) (ksp : t.sp = s.sp) (h2 : Reg.r2 ∉ regs)
    (h10 : Reg.r10 ∉ regs) (h11 : Reg.r11 ∉ regs) (h29 : Reg.r29 ∉ regs) (h31 : Reg.r31 ∉ regs)
    (hb : word t.mem p.B (8 * hBad) = 0#64 ↔ B') (sy : t.syms = s.syms) : MB p T x B' t := by
  have hdn := h.st.dims.n
  have hn' := h.st.dims.n'
  have hb1 := h.st.dims.b1
  have hb2 := h.st.dims.b2
  have hsl : slot (wOf p.bits) 0 = 256 := by simp [slot, hdrBytes]
  have hLe : p.L = (p.bits + 7) / 8 := rfl
  have hwe : wOf p.bits = (p.bits + 63) / 64 := rfl
  have hZe : p.Z = 8 * p.n := rfl
  have hw128 : wOf p.bits ≤ 128 := by rw [hwe]; omega_arith
  have st := h.st.step' (Frm.toMut hf fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact InMut.hdr (i := 26) (by decide)
    · exact InMut.hdr (i := 25) (by decide)) kg krd kwr ksp h31 h2
  have ew : ∀ d, d + 8 ≤ 200 ∨ 216 ≤ d → d + 8 ≤ 2 ^ 64 → word t.mem p.B d = word s.mem p.B d := fun d hd hd' =>
    hf.word_eq (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> dsimp only <;> omega_arith) hd'
  refine ⟨st, h.ph.keep (kg _ h10) (kg _ h11) (kg _ h29) fun d hd => ew d ?_ ?_,
    (ew 152 (by decide) (by decide)).trans h.u, ?_, hb, h.tab.step sy hf (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> dsimp only <;> omega_arith) krd⟩
  · have es : ∀ j, slot (wOf p.bits) j = 256 + j * (8 * (wOf p.bits + 2)) := fun _ => rfl
    unfold Read at hd
    rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | ⟨j, hj, rfl⟩ | rfl | rfl <;>
      first | omega_arith | (rw [es]; omega_arith)
  · have es : ∀ j, slot (wOf p.bits) j = 256 + j * (8 * (wOf p.bits + 2)) := fun _ => rfl
    unfold Read at hd
    rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | ⟨j, hj, rfl⟩ | rfl | rfl <;>
      first | omega_arith | (rw [es]; simp only [PP.Z] at *; omega_arith)
  · rw [hf.wv_eq (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> rw [hsl] <;> exact .inr (by decide)) (by rw [hsl]; omega_arith)]
    exact h.n

end VG.Proof.Ffdh.PPC64LE.ParameterCandidate
