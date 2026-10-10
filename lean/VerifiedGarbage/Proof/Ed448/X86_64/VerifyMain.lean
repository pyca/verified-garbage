import VerifiedGarbage.Proof.Ed448.X86_64.VerifyDecode
import VerifiedGarbage.Proof.Ed448.X86_64.VerifyLoop
import VerifiedGarbage.Proof.Ed448.X86_64.VerifyBits
import VerifiedGarbage.Proof.Ed448.X86_64.BaseConst
import VerifiedGarbage.Proof.Ed448.X86_64.BaseMain
import VerifiedGarbage.TCB.X86_64.Target
import VerifiedGarbage.Proof.Framework.X86_64.Abi
import VerifiedGarbage.Proof.Ed448.X86_64.VerifyLocal

/-!
# Ed448 verification's equation on x86-64: the whole function

The correctness of `vg_ed448_verify_equation` against the contract the proof
is written against (`verifyEquationLocal`, `VerifyLocal.lean`): `BAD` ends as the OR of
the checks of `S`, of decoding `A` and `R`, and of the comparison of `[4]Q`
with `[4]R`, for `Q` the reference ladder's `[S]B + [k](-A)` (`vladder`), which
decides the equation when `A` and `R` decode (`VerifyEqOk`, as decoding
`RecoverOk`, passed in by the registration files);
every write is in the working space, so the inputs are read unchanged, the
callee-saved registers are restored from it, and the return address is kept.
-/

namespace VG.Proof.Ed448.X86_64

open VG VG.X86_64 VG.Impl.Ed448 VG.Impl.Ed448.X86_64 VG.Proof.Ed448
open VG.Proof.X448.X86_64 (Scr Index Env E F fe Keep FieldOk word off Outside Outside2 ofs Saved clob copyOut_ok
  writeW_outside word_writeW_self contains_sc E_outside)
open VG.Impl.X448.X86_64 (W w sc at_ slot BITS copyOut)

/-- One store of `r` at `[b + d]`, `b` the working space. -/
theorem store1_ok {s : State} {base : Addr} (b r : Reg) (hb : s.gpr b = base)
    (hw : (⟨base, 8192⟩ : Region) ∈ s.wr) {d : Nat} (hd : d + 8 ≤ 8192) :
    WP isa (.block ([.store (at_ b d) r] : List Instr)) s fun t =>
      t.mem = s.mem.writeW (off base d) (s.gpr r) ∧ t.gpr = s.gpr ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  have w : InRegions s.wr (base + BitVec.ofNat 64 d) 8 := ⟨_, hw, contains_sc hd⟩
  erun [hb, w]

/-- `rsi = [rdi + d]`. -/
theorem movRsi_ok {s : State} {base : Addr} (hs : Scr s base) {d : Nat} (hd : d + 8 ≤ 8192) :
    WP isa (.block ([.mov .rsi (.mem (sc d))] : List Instr)) s fun t =>
      t.gpr .rsi = word s.mem base d ∧ (∀ r, r ≠ .rsi → t.gpr r = s.gpr r) ∧ t.mem = s.mem ∧
        t.rd = s.rd ∧ t.wr = s.wr := by
  have rb : InRegions (s.rd ++ s.wr) (base + BitVec.ofNat 64 d) 8 := hs.read hd
  erun [hs.rdi, rb]
  exact fun r hr => by simp only [hr, ite_false]

/-- `rdx = [rdi + BAD]`, then `rdx = (rdx == 0)` into `rax`. -/
theorem result_ok {s : State} {base : Addr} (hs : Scr s base) :
    WP isa (.block (([.mov .rdx (.mem (sc BAD))] : List Instr) ++ (isZero ++
      ([.mov .rax (.reg .rdx)] : List Instr)))) s fun t =>
      t.gpr .rax = (if word s.mem base BAD = 0 then 1 else 0) ∧
      (∀ r, r ≠ .rax → r ≠ .rdx → t.gpr r = s.gpr r) ∧ t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  have rb : InRegions (s.rd ++ s.wr) (base + BitVec.ofNat 64 BAD) 8 := hs.read (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (show WP isa (.block ([.mov .rdx (.mem (sc BAD))] : List Instr)) s fun t =>
      t.gpr .rdx = word s.mem base BAD ∧ (∀ r, r ≠ .rdx → t.gpr r = s.gpr r) ∧ t.mem = s.mem ∧
        t.rd = s.rd ∧ t.wr = s.wr by
    erun [hs.rdi, rb]
    exact fun r hr => by simp only [hr, ite_false]) fun s1 ⟨d1, g1, m1, rd1, wr1⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (isZero_ok s1) fun s2 ⟨d2, m2, g2, rd2, wr2⟩ => ?_
  refine WP.mono (show WP isa (.block ([.mov .rax (.reg .rdx)] : List Instr)) s2 fun t =>
      t.gpr .rax = s2.gpr .rdx ∧ (∀ r, r ≠ .rax → t.gpr r = s2.gpr r) ∧ t.mem = s2.mem ∧
        t.rd = s2.rd ∧ t.wr = s2.wr by
    erun
    exact fun r hr => by simp only [hr, ite_false]) fun t ⟨at', gt, mt, rdt, wrt⟩ => ?_
  refine ⟨by rw [at', d2, d1], fun r h1 h2 => by rw [gt r h1, g2 r h2, g1 r h2], by rw [mt, m2, m1],
    by rw [rdt, rd2, rd1], by rw [wrt, wr2, wr1]⟩

theorem zero_or64 (x : BitVec 64) : 0 ||| x = x := BitVec.zero_or

/-- `rsi = r9 + 57`. -/
theorem movR957_ok (s : State) :
    WP isa (.block ([.mov .rsi (.reg .r9), .alu .add .rsi (.imm 57)] : List Instr)) s fun t =>
      t.gpr .rsi = s.gpr .r9 + BitVec.ofNat 64 57 ∧ (∀ r, r ≠ .rsi → t.gpr r = s.gpr r) ∧
        t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  erun
  exact ⟨rfl, fun r hr => by simp only [hr, ite_false]⟩

/-- `rax = 0`. -/
theorem movRax0_ok (s : State) :
    WP isa (.block ([.mov32 .rax (.imm 0)] : List Instr)) s fun t =>
      t.gpr .rax = 0 ∧ (∀ r, r ≠ .rax → t.gpr r = s.gpr r) ∧ t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  erun
  exact fun r hr => by simp only [hr, ite_false]

/-- The moves of the entry. -/
theorem movArgs_ok (s : State) :
    WP isa (.block ([.mov .r8 (.reg .rdi), .mov .r9 (.reg .rsi), .mov .rdi (.reg .rcx),
      .mov .rsi (.reg .rdx)] : List Instr)) s fun t =>
      t.gpr .r8 = s.gpr .rdi ∧ t.gpr .r9 = s.gpr .rsi ∧ t.gpr .rdi = s.gpr .rcx ∧
      t.gpr .rsi = s.gpr .rdx ∧ (∀ r, r ∉ [Reg.r8, .r9, .rdi, .rsi] → t.gpr r = s.gpr r) ∧
      t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  erun
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [hr.1, hr.2.1, hr.2.2.1, hr.2.2.2, ite_false]

/-- What the entry leaves: the callee-saved registers saved, the pointers to `A` and the
signature in `r8` and `r9`, and the challenge's in `rsi`. -/
theorem ventry_ok {s : State} {base : Addr} (hbase : s.gpr .rcx = base)
    (hws : (⟨base, 8192⟩ : Region) ∈ s.wr) (hn : base.toNat + 8192 ≤ 2 ^ 64) :
    WP isa (.block ventry) s fun t =>
      Scr t base ∧ Saved base s.gpr t.mem ∧ t.gpr .r8 = s.gpr .rdi ∧ t.gpr .r9 = s.gpr .rsi ∧
      t.gpr .rsi = s.gpr .rdx ∧ (∀ r, r ∉ [Reg.r8, .r9, .rdi, .rsi] → t.gpr r = s.gpr r) ∧
      Outside base 0 48 s.mem t.mem ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  rw [ventry, WP.block_append_iff]
  refine WP.mono (saveAt_ok .rcx hbase hws) fun s1 ⟨g1, rd1, wr1, o1, sv1⟩ => ?_
  refine WP.mono (movArgs_ok s1) fun t ⟨r8t, r9t, dit, sit, gt, mt, rdt, wrt⟩ => ?_
  refine ⟨⟨by rw [dit, g1, hbase], by rw [wrt, wr1]; exact hws, hn⟩, by rw [mt]; exact sv1,
    by rw [r8t, g1], by rw [r9t, g1], by rw [sit, g1], fun r hr => by rw [gt r hr, g1], by rw [mt]; exact o1,
    by rw [rdt, rd1], by rw [wrt, wr1]⟩

/-- The bits of `k` at `KBITS` and of `S` at `BITS`, and `rsi` the address of `S`. -/
theorem vbits_ok {s : State} {base sig ch : Addr} (hs : Scr s base) (hch : s.gpr .rsi = ch)
    (hsig : s.gpr .r9 = sig)
    (hrs : ∀ q < 57, InRegions (s.rd ++ s.wr) (sig + BitVec.ofNat 64 57 + BitVec.ofNat 64 q) 1)
    (hrc : ∀ q < 57, InRegions (s.rd ++ s.wr) (ch + BitVec.ofNat 64 q) 1)
    (hfs : ∀ q < 57, 8192 ≤ ofs base (sig + BitVec.ofNat 64 57 + BitVec.ofNat 64 q))
    (hfc : ∀ q < 57, 8192 ≤ ofs base (ch + BitVec.ofNat 64 q)) :
    WP isa vbits s fun t =>
      (∀ n < 456, t.mem (off base (BITS + n)) = BitVec.ofNat 8
        ((Spec.Ed448.decodeLE (Spec.Ed448.bytesAt s.mem (sig + BitVec.ofNat 64 57) 57) >>> n) &&& 1)) ∧
      (∀ n < 456, t.mem (off base (KBITS + n)) = BitVec.ofNat 8
        ((Spec.Ed448.decodeLE (Spec.Ed448.bytesAt s.mem ch 57) >>> n) &&& 1)) ∧
      t.gpr .rsi = sig + BitVec.ofNat 64 57 ∧
      (∀ r, r ∉ [Reg.rax, .rdx, .rbx, .rsi] → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      Outside base BITS 968 s.mem t.mem := by
  rw [vbits]
  apply WP.seq
  refine WP.mono (bitsAt_ok (o := KBITS) (by decide) hs hch hrc hfc) fun s1 ⟨g1, rd1, wr1, o1, b1⟩ => ?_
  have hs1 : Scr s1 base := ⟨(g1 _ (by decide)).trans hs.rdi, wr1 ▸ hs.wr, hs.nowrap⟩
  apply WP.seq
  refine WP.mono (movR957_ok s1) fun s2 ⟨si2, g2, m2, rd2, wr2⟩ => ?_
  have hs2 : Scr s2 base := ⟨(g2 _ (by decide)).trans hs1.rdi, wr2 ▸ hs1.wr, hs1.nowrap⟩
  have hsig2 : s2.gpr .rsi = sig + BitVec.ofNat 64 57 := by rw [si2, g1 _ (by decide), hsig]
  refine WP.mono (bitsAt_ok (o := BITS) (by decide) hs2 hsig2
    (fun q hq => by rw [rd2, wr2, rd1, wr1]; exact hrs q hq) hfs) fun t ⟨gt, rdt, wrt, ot, bt⟩ => ?_
  have hm2 : ∀ x, 8192 ≤ ofs base x → s2.mem x = s.mem x := fun x hx => by
    rw [m2, o1 x (Or.inr (by simp only [KBITS]; omega))]
  have h3 : ∀ r, r ∉ [Reg.rax, .rdx, .rbx, .rsi] → r ∉ [Reg.rax, .rdx, .rbx] := fun r hr h =>
    hr (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h ⊢
      rcases h with h | h | h <;> simp only [h, true_or, or_true])
  refine ⟨fun n hn => ?_, fun n hn => ?_, by rw [gt _ (by decide), hsig2], fun r hr => ?_,
    by rw [rdt, rd2, rd1], by rw [wrt, wr2, wr1], fun x hx => ?_⟩
  · rw [bt n hn, hm2 _ (hfs _ (by omega)), scalar_bit s.mem _ hn]
  · have hlt : KBITS + n < 2 ^ 64 := by simp only [KBITS]; omega
    have hofs := VG.Proof.X448.X86_64.ofs_off' base hlt
    rw [ot _ (Or.inr (by rw [hofs]; simp only [BITS, KBITS]; omega)), m2, b1 n hn, scalar_bit s.mem _ hn]
  · have hsi : r ≠ .rsi := fun h => hr (by simp [h])
    rw [gt r (h3 r hr), g2 r hsi, g1 r (h3 r hr)]
  · simp only [BITS] at hx
    rw [ot x (by simp only [BITS]; omega), m2, o1 x (by simp only [KBITS]; omega)]

theorem vstart_eq : vstart = ([.store (sc PPK) .r8] : List Instr) ++ (([.store (sc PSIG) .r9] : List Instr) ++
    (([.mov32 .rax (.imm 0)] : List Instr) ++ (([.store (sc BAD) .rax] : List Instr) ++ sCheck))) := rfl

/-- The pointers to `A` and the signature saved, and `BAD` the check of `S < L`. -/
theorem vstart_ok {s : State} {base pk sig : Addr} (hs : Scr s base) (hpk : s.gpr .r8 = pk)
    (hsig : s.gpr .r9 = sig) (hp : s.gpr .rsi = sig + BitVec.ofNat 64 57)
    (hr8 : ∀ i < 7, InRegions (s.rd ++ s.wr) (sig + BitVec.ofNat 64 57 + BitVec.ofNat 64 (8 * i)) 8)
    (hr56 : InRegions (s.rd ++ s.wr) (sig + BitVec.ofNat 64 57 + BitVec.ofNat 64 56) 1)
    (hfar : ∀ i < 57, 8192 ≤ ofs base (sig + BitVec.ofNat 64 57 + BitVec.ofNat 64 i)) :
    WP isa (.block vstart) s fun t =>
      word t.mem base PPK = pk ∧ word t.mem base PSIG = sig ∧
      (∃ c : BitVec 64, (c = 0 ↔ Spec.Ed448.decodeLE (Spec.Ed448.bytesAt s.mem
        (sig + BitVec.ofNat 64 57) 57) < Spec.Ed448.L) ∧ word t.mem base BAD = c) ∧
      (∀ r, r ∉ Reg.rax :: Reg.rdx :: W → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      Outside base KC 1568 s.mem t.mem := by
  have O3 : ∀ {m : Mem} {d : Nat} (v : BitVec 64), d + 8 < 2 ^ 64 → Outside base d 8 m (m.writeW (off base d) v) :=
    fun v h => writeW_outside _ base v h
  rw [vstart_eq, WP.block_append_iff]
  refine WP.mono (store1_ok .rdi .r8 hs.rdi hs.wr (d := PPK) (by decide)) fun s1 ⟨m1, g1, rd1, wr1⟩ => ?_
  have hs1 : Scr s1 base := ⟨by rw [g1]; exact hs.rdi, wr1 ▸ hs.wr, hs.nowrap⟩
  rw [WP.block_append_iff]
  refine WP.mono (store1_ok .rdi .r9 hs1.rdi hs1.wr (d := PSIG) (by decide)) fun s2 ⟨m2, g2, rd2, wr2⟩ => ?_
  have hs2 : Scr s2 base := ⟨by rw [g2]; exact hs1.rdi, wr2 ▸ hs1.wr, hs.nowrap⟩
  rw [WP.block_append_iff]
  refine WP.mono (movRax0_ok s2) fun s3 ⟨ax3, g3, m3, rd3, wr3⟩ => ?_
  have hs3 : Scr s3 base := ⟨(g3 _ (by decide)).trans hs2.rdi, wr3 ▸ hs2.wr, hs.nowrap⟩
  rw [WP.block_append_iff]
  refine WP.mono (store1_ok .rdi .rax hs3.rdi hs3.wr (d := BAD) (by decide)) fun s4 ⟨m4, g4, rd4, wr4⟩ => ?_
  have hs4 : Scr s4 base := ⟨by rw [g4]; exact hs3.rdi, wr4 ▸ hs3.wr, hs.nowrap⟩
  have hp4 : s4.gpr .rsi = sig + BitVec.ofNat 64 57 := by
    rw [g4, g3 _ (by decide), g2, g1, hp]
  have rr4 : s4.rd ++ s4.wr = s.rd ++ s.wr := by rw [rd4, wr4, rd3, wr3, rd2, wr2, rd1, wr1]
  have O4 : ∀ x, 8192 ≤ ofs base x → s4.mem x = s.mem x := fun x hx => by
    rw [m4, O3 _ (by decide) x (Or.inr (by simp only [BAD]; omega)), m3, m2,
      O3 _ (by decide) x (Or.inr (by simp only [PSIG]; omega)), m1,
      O3 _ (by decide) x (Or.inr (by simp only [PPK]; omega))]
  refine WP.mono (sCheck_ok hs4 hp4 (by rw [rr4]; exact hr8) (by rw [rr4]; exact hr56) hfar)
    fun t ⟨c, hc, bt, gt, rdt, wrt, ot⟩ => ?_
  have hbytes : Spec.Ed448.bytesAt s4.mem (sig + BitVec.ofNat 64 57) 57 =
      Spec.Ed448.bytesAt s.mem (sig + BitVec.ofNat 64 57) 57 := by
    simp only [Spec.Ed448.bytesAt]
    exact List.map_congr_left fun i hi => O4 _ (hfar i (List.mem_range.mp hi))
  have keepW : ∀ d, d + 8 ≤ BAD → KC + 56 ≤ d → word t.mem base d = word s4.mem base d := fun d h1 h2 =>
    ot.word (Or.inr h2) (Or.inl h1) (by simp only [BAD] at h1; omega)
  refine ⟨?_, ?_, ⟨c, by rw [hc, hbytes], ?_⟩, fun r hr => ?_, by rw [rdt, rd4, rd3, rd2, rd1],
    by rw [wrt, wr4, wr3, wr2, wr1], fun x hx => ?_⟩
  · rw [keepW PPK (by decide) (by decide), m4, (O3 _ (by decide)).word (Or.inl (by decide)) (by decide), m3,
      m2, (O3 _ (by decide)).word (Or.inl (by decide)) (by decide), m1, word_writeW_self, hpk]
  · rw [keepW PSIG (by decide) (by decide), m4, (O3 _ (by decide)).word (Or.inl (by decide)) (by decide), m3,
      m2, word_writeW_self, g1, hsig]
  · rw [bt, m4, word_writeW_self, ax3, zero_or64]
  · rw [gt r hr, g4, g3 r (fun h => hr (h ▸ List.mem_cons_self)), g2, g1]
  · simp only [KC] at hx
    rw [ot x (by simp only [KC]; omega) (by simp only [BAD]; omega), m4,
      O3 _ (by decide) x (by simp only [BAD]; omega), m3, m2,
      O3 _ (by decide) x (by simp only [PSIG]; omega), m1,
      O3 _ (by decide) x (by simp only [PPK]; omega)]

theorem bytesAt_take57 (m : Mem) (p : Addr) :
    (Spec.Ed448.bytesAt m p 114).take 57 = Spec.Ed448.bytesAt m p 57 := by
  simp [Spec.Ed448.bytesAt, ← List.map_take, List.take_range]

theorem bytesAt_drop57 (m : Mem) (p : Addr) :
    (Spec.Ed448.bytesAt m p 114).drop 57 = Spec.Ed448.bytesAt m (p + BitVec.ofNat 64 57) 57 := by
  refine List.ext_getElem (by simp [Spec.Ed448.bytesAt]) fun i _ _ => ?_
  simp only [Spec.Ed448.bytesAt, List.getElem_drop, List.getElem_map, List.getElem_range]
  rw [Offset.add_add]

theorem bytesAt114_len (m : Mem) (p : Addr) : (Spec.Ed448.bytesAt m p 114).length = 57 + 57 := by
  simp [Spec.Ed448.bytesAt]

/-- Bytes far from the working space, after writes only to it. -/
theorem far_bytes {base p : Addr} {n : Nat} {m m' : Mem} (h : Outside base 0 8192 m m')
    (hf : ∀ i < n, 8192 ≤ ofs base (p + BitVec.ofNat 64 i)) :
    Spec.Ed448.bytesAt m' p n = Spec.Ed448.bytesAt m p n := by
  simp only [Spec.Ed448.bytesAt]
  exact List.map_congr_left fun i hi => h _ (Or.inr (by have := hf i (List.mem_range.mp hi); omega))

variable {fld : Impl.X448.X86_64.Field} (hf : FieldOk fld)

variable {P : Point64.Ops} (hP : Point64.PointOk P)

include hP in
/-- The point in slots 0–2 doubled twice; slots 3–11 kept. -/
theorem vdouble_ok {s : State} {base : Addr} (hs : Scr s base) :
    WP isa (vdouble P) s fun t => (∀ r, r ∉ .rbx :: clob → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧
      t.wr = s.wr ∧ Outside base 64 1584 s.mem t.mem ∧
      pt (E t.mem base) 0 1 2 = Proof.Ed448.double (Proof.Ed448.double (pt (E s.mem base) 0 1 2)) ∧
      ∀ i : Index, 3 ≤ i.val ∧ i.val < 12 → E t.mem base i = E s.mem base i := by
  unfold vdouble
  refine WP.seq (WP.mono (show WP isa (.block [.mov32 .rbx (.imm (BitVec.ofNat 32 2))]) s _ from
    Proof.X448.X86_64.setRbx_ok s 2 (by decide)) fun s₁ ⟨e₁, g₁, m₁, r₁, w₁⟩ => ?_)
  refine WP.loop (M := isa) (fun m (t : State) => 1 ≤ m ∧ m ≤ 2 ∧ t.gpr .rbx = BitVec.ofNat 64 m ∧
      (∀ r, r ∉ .rbx :: clob → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      Outside base 64 1584 s.mem t.mem ∧
      pt (E t.mem base) 0 1 2 = (if m = 2 then id else Proof.Ed448.double) (pt (E s.mem base) 0 1 2) ∧
      ∀ i : Index, 3 ≤ i.val ∧ i.val < 12 → E t.mem base i = E s.mem base i)
    ?_ 2 s₁ ⟨by decide, by decide, e₁, fun r hr => g₁ r (fun h => hr (by simp [h])), r₁, w₁,
      by rw [m₁]; exact Outside.refl _ _ _ _, by rw [m₁]; rfl, fun _ _ => by rw [m₁]⟩
  intro m t ⟨h1, h2, et, gt, rt, wt, ot, qt, kt⟩
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  have ht : Scr t base := ⟨(gt _ (by decide)).trans hs.rdi, wt ▸ hs.wr, hs.nowrap⟩
  refine WP.seq (WP.mono (hP.dbl ht) fun v ⟨kv, ev⟩ => ?_)
  refine WP.mono (Proof.X448.X86_64.decRbx_ok (k := k) (by omega) (by rw [kv.gpr _ (by decide), et]))
    fun u ⟨eu, gu, mu, ru, wu, zu⟩ => ?_
  have gu' : ∀ r, r ∉ .rbx :: clob → u.gpr r = s.gpr r := fun r hr => by
    rw [gu r (fun h => hr (by simp [h])), kv.gpr r (fun h => hr (List.mem_cons_of_mem _ h)), gt r hr]
  have ou' : Outside base 64 1584 s.mem u.mem := fun x hx => by
    rw [mu, kv.mem x hx, ot x hx]
  have qu : pt (E u.mem base) 0 1 2 = Proof.Ed448.double (pt (E t.mem base) 0 1 2) := by
    rw [mu, ev]; exact doubleOps_eval _
  have ku : ∀ i : Index, 3 ≤ i.val ∧ i.val < 12 → E u.mem base i = E s.mem base i := fun i hi => by
    rw [mu, ev, doubleOps_keep _ _ (Or.inl hi), kt i hi]
  simp only [eval, zu, Option.map_some]
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · refine .inl ⟨rfl, gu', ru.trans (kv.rd.trans rt), wu.trans (kv.wr.trans wt), ou', ?_, ku⟩
    rw [qu, qt]; rfl
  · have k1 : k = 1 := by omega
    subst k1
    refine .inr ⟨rfl, 1, by omega, by omega, by omega, eu, gu', ru.trans (kv.rd.trans rt),
      wu.trans (kv.wr.trans wt), ou', by rw [qu, qt]; rfl, ku⟩

/-- `RX`, or `RY`, copied into slot `i`. -/
theorem copyIn_ok {s : State} {base : Addr} (hs : Scr s base) (i : Index) {a : Nat} (ha' : a + 56 ≤ 8192) :
    WP isa (.block (copyOut (slot i.val) a)) s fun t =>
      Keep base s t ∧ E t.mem base = Function.update (E s.mem base) i (F s.mem base a) := by
  have hW : ∀ x ∈ W, x ∈ clob := by decide
  have hi := Proof.X448.X86_64.slot_lt i
  have gi := Proof.X448.X86_64.slot_ge i
  simp only [Impl.X448.X86_64.ACC] at hi
  refine WP.mono (copyOut_ok hs (by omega) ha') fun t ⟨ft, ot, gt, rdt, wrt⟩ =>
    ⟨⟨fun r hr => gt r (fun h => hr (hW r h)), rdt, wrt, ot.mono (by omega) (by omega)⟩, ?_⟩
  funext k
  by_cases hk : k = i
  · subst hk
    rw [Function.update_self]
    show VG.Proof.X448.toFe (fe t.mem base (slot k.val)) = VG.Proof.X448.toFe (fe s.mem base a)
    rw [ft]
  · rw [Function.update_of_ne hk]
    exact E_outside ot k (Proof.X448.X86_64.slot_sep hk)

/-- `[4]Q` (slots 0–2) into slots 3–5, and `R` (`RX`, `RY`, 1) into slots 0–2. -/
theorem vR_ok {s : State} {base : Addr} (hs : Scr s base) :
    WP isa (.block vR) s fun t =>
      Keep base s t ∧ pt (E t.mem base) 3 4 5 = pt (E s.mem base) 0 1 2 ∧
      pt (E t.mem base) 0 1 2 = ⟨F s.mem base RX, F s.mem base RY, 1⟩ ∧
      ∀ i : Index, 6 ≤ i.val → E t.mem base i = E s.mem base i := by
  rw [vR, WP.block_append_iff]
  refine WP.mono (copySlot_ok hs 3 0) fun s1 ⟨k1, e1⟩ => ?_
  have hs1 := k1.scr hs
  rw [WP.block_append_iff]
  refine WP.mono (copySlot_ok hs1 4 1) fun s2 ⟨k2, e2⟩ => ?_
  have hs2 := k2.scr hs1
  rw [WP.block_append_iff]
  refine WP.mono (copySlot_ok hs2 5 2) fun s3 ⟨k3, e3⟩ => ?_
  have hs3 := k3.scr hs2
  rw [WP.block_append_iff]
  refine WP.mono (copyIn_ok hs3 0 (a := RX) (by decide)) fun s4 ⟨k4, e4⟩ => ?_
  have hs4 := k4.scr hs3
  rw [WP.block_append_iff]
  refine WP.mono (copyIn_ok hs4 1 (a := RY) (by decide)) fun s5 ⟨k5, e5⟩ => ?_
  have hs5 := k5.scr hs4
  refine WP.mono (constE_ok hs5 2 1 c1) fun t ⟨kt, et⟩ => ?_
  have fx : F s3.mem base RX = F s.mem base RX := by
    show VG.Proof.X448.toFe (fe s3.mem base RX) = VG.Proof.X448.toFe (fe s.mem base RX)
    rw [((k1.mem.trans k2.mem).trans k3.mem).fe (Or.inr (by decide)) (by decide)]
  have fy : F s4.mem base RY = F s.mem base RY := by
    show VG.Proof.X448.toFe (fe s4.mem base RY) = VG.Proof.X448.toFe (fe s.mem base RY)
    rw [(((k1.mem.trans k2.mem).trans k3.mem).trans k4.mem).fe (Or.inr (by decide)) (by decide)]
  refine ⟨((((k1.trans k2).trans k3).trans k4).trans k5).trans kt, ?_, ?_, fun i hi => ?_⟩
  · rw [et, e5, e4, e3, e2, e1]; rfl
  · rw [et, e5, e4, fx, fy]; rfl
  · have ne : ∀ j : Index, j.val < 6 → i ≠ j := fun j hj h => by subst h; omega
    rw [et, e5, e4, e3, e2, e1, Function.update_of_ne (ne 2 (by decide)), Function.update_of_ne (ne 1 (by decide)),
      Function.update_of_ne (ne 0 (by decide)), Function.update_of_ne (ne 5 (by decide)),
      Function.update_of_ne (ne 4 (by decide)), Function.update_of_ne (ne 3 (by decide))]

include hf hP in
theorem vfinish_ok {s : State} {base : Addr} (hs : Scr s base) {g : Reg → BitVec 64}
    (hsv : Saved base g s.mem) :
    WP isa (vfinish fld P) s fun t =>
      t.gpr .rax = (if word s.mem base BAD = 0 ∧ Spec.Ed448.pointEqual
        (Proof.Ed448.double (Proof.Ed448.double (pt (E s.mem base) 0 1 2)))
        (Proof.Ed448.double (Proof.Ed448.double ⟨F s.mem base RX, F s.mem base RY, 1⟩)) = true then 1 else 0) ∧
      (∀ rd ∈ Impl.X448.X86_64.saved, t.gpr rd.1 = g rd.1) ∧
      (∀ r, r ∉ .rbx :: clob → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      Outside2 base 64 1584 BAD 80 s.mem t.mem := by
  rw [vfinish]
  refine WP.seq (WP.mono (vdouble_ok hP hs) fun sa ⟨ga, rda, wra, oa, qa, _⟩ => ?_)
  have hsa : Scr sa base := ⟨(ga _ (by decide)).trans hs.rdi, wra ▸ hs.wr, hs.nowrap⟩
  refine WP.seq (WP.mono (vR_ok hsa) fun sb ⟨kb, qb, rb, _⟩ => ?_)
  have hsb := kb.scr hsa
  refine WP.seq (WP.mono (vdouble_ok hP hsb) fun sd ⟨gd', rdd', wrd', od', pd', kd'⟩ => ?_)
  have hsd : Scr sd base := ⟨(gd' _ (by decide)).trans hsb.rdi, wrd' ▸ hsb.wr, hsb.nowrap⟩
  have gd : ∀ r, r ∉ .rbx :: clob → sd.gpr r = s.gpr r := fun r hr => by
    rw [gd' r hr, kb.gpr r (fun h => hr (List.mem_cons_of_mem _ h)), ga r hr]
  have rdd : sd.rd = s.rd := by rw [rdd', kb.rd, rda]
  have wrd : sd.wr = s.wr := by rw [wrd', kb.wr, wra]
  have od : Outside base 64 1584 s.mem sd.mem := (oa.trans kb.mem).trans od'
  have fx : F sa.mem base RX = F s.mem base RX := by
    show VG.Proof.X448.toFe (fe sa.mem base RX) = VG.Proof.X448.toFe (fe s.mem base RX)
    rw [oa.fe (Or.inr (by decide)) (by decide)]
  have fy : F sa.mem base RY = F s.mem base RY := by
    show VG.Proof.X448.toFe (fe sa.mem base RY) = VG.Proof.X448.toFe (fe s.mem base RY)
    rw [oa.fe (Or.inr (by decide)) (by decide)]
  have qd : pt (E sd.mem base) 3 4 5 = Proof.Ed448.double (Proof.Ed448.double (pt (E s.mem base) 0 1 2)) := by
    rw [pt_congr (kd' 3 (by decide)) (kd' 4 (by decide)) (kd' 5 (by decide)), qb, qa]
  have pd : pt (E sd.mem base) 0 1 2 =
      Proof.Ed448.double (Proof.Ed448.double ⟨F s.mem base RX, F s.mem base RY, 1⟩) := by
    rw [pd', rb, fx, fy]
  rw [WP.block_append_iff]
  refine WP.mono (fieldCode_ok hf [.mul 12 3 2, .mul 13 0 5] (by decide) hsd) fun s1 ⟨k1', e1'⟩ => ?_
  have hs1 := k1'.scr hsd
  have k1 : Keep base sd s1 := k1'
  have h4 : ∀ i : Index, i.val < 6 → E s1.mem base i = E sd.mem base i :=
    fun i hi => by
      rw [e1']
      exact evalOps_keep _ _ _ fun op hop => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hop
        rcases hop with rfl | rfl <;> simp only [fopDest] <;> omega
  have q1 : pt (E s1.mem base) 3 4 5 = Proof.Ed448.double (Proof.Ed448.double (pt (E s.mem base) 0 1 2)) := by
    rw [pt_congr (h4 3 (by decide)) (h4 4 (by decide)) (h4 5 (by decide)), qd]
  have r1 : pt (E s1.mem base) 0 1 2 =
      Proof.Ed448.double (Proof.Ed448.double ⟨F s.mem base RX, F s.mem base RY, 1⟩) := by
    rw [pt_congr (h4 0 (by decide)) (h4 1 (by decide)) (h4 2 (by decide)), pd]
  have x12 : E s1.mem base 12 = E s1.mem base 3 * E s1.mem base 2 := by
    rw [h4 3 (by decide), h4 2 (by decide), e1']; rfl
  have x13 : E s1.mem base 13 = E s1.mem base 0 * E s1.mem base 5 := by
    rw [h4 0 (by decide), h4 5 (by decide), e1']; rfl
  rw [WP.block_append_iff]
  refine WP.mono (eqSlots_ok hs1 12 13) fun s2 ⟨c4, hc4, b2, k2, _⟩ => ?_
  have hs2 := k2.scr hs1
  rw [WP.block_append_iff]
  refine WP.mono (fieldCode_ok hf [.mul 12 4 2, .mul 13 1 5] (by decide) hs2) fun s3 ⟨k3, e3⟩ => ?_
  have hs3 := k3.scr hs2
  rw [WP.block_append_iff]
  refine WP.mono (eqSlots_ok hs3 12 13) fun s4 ⟨c5, hc5, b4, k4, _⟩ => ?_
  have hs4 := k4.scr hs3
  rw [← List.append_assoc, ← List.append_assoc, WP.block_append_iff, List.append_assoc]
  refine WP.mono (result_ok hs4) fun s5 ⟨a5, g5, m5, rd5, wr5⟩ => ?_
  have hs5 : Scr s5 base := ⟨(g5 _ (by decide) (by decide)).trans hs4.rdi, wr5 ▸ hs4.wr, hs4.nowrap⟩
  have sv5 : Saved base g s5.mem := by
    rw [m5]
    exact (((((hsv.outside od (by decide)).outside k1.mem (by decide)).outside k2.mem (by decide)).outside k3.mem (by decide)).outside
      k4.mem (by decide))
  refine WP.mono (Proof.X448.X86_64.restore_ok hs5 sv5) fun t ⟨rt, gt, mt, rdt, wrt⟩ => ?_
  -- the values
  have e2 : E s2.mem base = E s1.mem base := k2.E
  have y12 : E s3.mem base 12 = E s1.mem base 4 * E s1.mem base 2 := by rw [e3, e2]; rfl
  have y13 : E s3.mem base 13 = E s1.mem base 1 * E s1.mem base 5 := by rw [e3, e2]; rfl
  have hpe : Spec.Ed448.pointEqual (pt (E s1.mem base) 3 4 5) (pt (E s1.mem base) 0 1 2) = true ↔
      (E s1.mem base 3 * E s1.mem base 2 = E s1.mem base 0 * E s1.mem base 5 ∧
        E s1.mem base 4 * E s1.mem base 2 = E s1.mem base 1 * E s1.mem base 5) := by
    simp only [Spec.Ed448.pointEqual, pt, Bool.and_eq_true, beq_iff_eq]
  have hb : word s4.mem base BAD = word s.mem base BAD ||| c4 ||| c5 := by
    rw [b4, k3.mem.word (Or.inr (by decide)) (by decide), b2, k1.mem.word (Or.inr (by decide)) (by decide),
      od.word (Or.inr (by decide)) (by decide)]
  refine ⟨?_, rt, fun r hr => ?_, ?_, ?_, ?_⟩
  · have hcond : (word s.mem base BAD ||| c4 ||| c5 = 0) ↔ (word s.mem base BAD = 0 ∧
        Spec.Ed448.pointEqual (Proof.Ed448.double (Proof.Ed448.double (pt (E s.mem base) 0 1 2)))
          (Proof.Ed448.double (Proof.Ed448.double ⟨F s.mem base RX, F s.mem base RY, 1⟩)) = true) := by
      rw [or_eq_zero64, or_eq_zero64, hc5, hc4, y12, y13, x12, x13, ← q1, ← r1, hpe, and_assoc]
    rw [gt _ (by decide), a5, hb]
    exact if_congr hcond rfl rfl
  · have hr' : r ∉ clob := fun h => hr (List.mem_cons_of_mem _ h)
    have s1' : ∀ x ∈ Reg.rax :: Reg.rdx :: Reg.r15 :: W, x ∈ clob := by decide
    rw [gt r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
      refine ⟨fun h => hr (h ▸ List.mem_cons_self), fun h => hr' (h ▸ by decide), fun h => hr' (h ▸ by decide),
        fun h => hr' (h ▸ by decide), fun h => hr' (h ▸ by decide), fun h => hr' (h ▸ by decide)⟩),
      g5 r (fun h => hr' (h ▸ by decide)) (fun h => hr' (h ▸ by decide)), k4.gpr r (fun h => hr' (s1' r h)),
      k3.gpr r hr', k2.gpr r (fun h => hr' (s1' r h)), k1.gpr r hr', gd r hr]
  · rw [rdt, rd5, k4.rd, k3.rd, k2.rd, k1.rd, rdd]
  · rw [wrt, wr5, k4.wr, k3.wr, k2.wr, k1.wr, wrd]
  · intro x h1 h2
    rw [mt, m5, k4.mem x h2, k3.mem x h1, k2.mem x h2, k1.mem x h1, od x h1]

/-! ## `R` and `A`, decoded by one loop -/

/-- Writes in the slots, or from `BAD` to `CNT`: `BAD`, `SIGN`, `NEG`, `CAN`, `R`'s place and
the loop's pointer and count. -/
abbrev DFrame (base : Addr) (m m' : Mem) : Prop := Outside2 base 64 1584 BAD 208 m m'

theorem DFrame.of2 {base : Addr} {m m' : Mem} (h : Outside2 base 64 1584 BAD 80 m m') : DFrame base m m' :=
  fun p h1 h2 => h p h1 (by simp only [BAD] at *; omega)

theorem DFrame.of1 {base : Addr} {m m' : Mem} {o n : Nat} (h : Outside base o n m m') (h1 : BAD ≤ o)
    (h2 : o + n ≤ BAD + 208) : DFrame base m m' := fun p _ hq => h p (by omega)

theorem DFrame.trans {base : Addr} {m₁ m₂ m₃ : Mem} (h₁ : DFrame base m₁ m₂) (h₂ : DFrame base m₂ m₃) :
    DFrame base m₁ m₃ := fun p hx hy => (h₂ p hx hy).trans (h₁ p hx hy)

/-- What a `DFrame` keeps, as one range. -/
theorem DFrame.wide {base : Addr} {m m' : Mem} (h : DFrame base m m') : Outside base 64 1832 m m' :=
  h.outside (by decide) (by decide) (by decide) (by decide)

/-- `r = [rdi + d]`. -/
theorem movMem_ok {s : State} {base : Addr} (hs : Scr s base) (r : Reg) {d : Nat} (hd : d + 8 ≤ 8192) :
    WP isa (.block ([.mov r (.mem (sc d))] : List Instr)) s fun t =>
      t.gpr r = word s.mem base d ∧ (∀ r', r' ≠ r → t.gpr r' = s.gpr r') ∧ t.mem = s.mem ∧
        t.rd = s.rd ∧ t.wr = s.wr := by
  have rb : InRegions (s.rd ++ s.wr) (base + BitVec.ofNat 64 d) 8 := hs.read hd
  erun [hs.rdi, rb]
  exact fun r' hr => by simp only [hr, ite_false]

/-- One store, keeping the flags. -/
theorem storeZ_ok {s : State} {base : Addr} (hs : Scr s base) (r : Reg) {d : Nat} (hd : d + 8 ≤ 8192) :
    WP isa (.block ([.store (sc d) r] : List Instr)) s fun t =>
      t.mem = s.mem.writeW (off base d) (s.gpr r) ∧ t.gpr = s.gpr ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
        t.zf = s.zf := by
  have w : InRegions s.wr (base + BitVec.ofNat 64 d) 8 := ⟨_, hs.wr, contains_sc hd⟩
  erun [hs.rdi, w]

theorem vdecodeInit_eq : ([.mov .rsi (.mem (sc PSIG)), .store (sc PCUR) .rsi, .mov32 .rbx (.imm 2),
    .store (sc CNT) .rbx] : List Instr) = ([.mov .rsi (.mem (sc PSIG))] : List Instr) ++
    (([.store (sc PCUR) .rsi] : List Instr) ++ (([.mov32 .rbx (.imm (BitVec.ofNat 32 2))] : List Instr) ++
    ([.store (sc CNT) .rbx] : List Instr))) := rfl

/-- The loop's pointer at `R`, and its count 2. -/
theorem vdecodeInit_ok {s : State} {base : Addr} (hs : Scr s base) :
    WP isa (.block ([.mov .rsi (.mem (sc PSIG)), .store (sc PCUR) .rsi, .mov32 .rbx (.imm 2),
      .store (sc CNT) .rbx] : List Instr)) s fun t =>
      word t.mem base PCUR = word s.mem base PSIG ∧ word t.mem base CNT = BitVec.ofNat 64 2 ∧
      Outside base PCUR 16 s.mem t.mem ∧ (∀ r, r ∉ [Reg.rsi, .rbx] → t.gpr r = s.gpr r) ∧
      t.rd = s.rd ∧ t.wr = s.wr := by
  rw [vdecodeInit_eq, WP.block_append_iff]
  refine WP.mono (movMem_ok hs .rsi (d := PSIG) (by decide)) fun s1 ⟨e1, g1, m1, rd1, wr1⟩ => ?_
  have hs1 : Scr s1 base := ⟨(g1 _ (by decide)).trans hs.rdi, wr1 ▸ hs.wr, hs.nowrap⟩
  rw [WP.block_append_iff]
  refine WP.mono (storeZ_ok hs1 .rsi (d := PCUR) (by decide)) fun s2 ⟨m2, g2, rd2, wr2, _⟩ => ?_
  have hs2 : Scr s2 base := ⟨by rw [g2]; exact hs1.rdi, wr2 ▸ hs1.wr, hs.nowrap⟩
  rw [WP.block_append_iff]
  refine WP.mono (Proof.X448.X86_64.setRbx_ok s2 2 (by decide)) fun s3 ⟨e3, g3, m3, rd3, wr3⟩ => ?_
  have hs3 : Scr s3 base := ⟨(g3 _ (by decide)).trans hs2.rdi, wr3 ▸ hs2.wr, hs.nowrap⟩
  refine WP.mono (storeZ_ok hs3 .rbx (d := CNT) (by decide)) fun t ⟨mt, gt, rdt, wrt, _⟩ =>
    ⟨?_, ?_, ?_, fun r hr => ?_, by rw [rdt, rd3, rd2, rd1], by rw [wrt, wr3, wr2, wr1]⟩
  · rw [mt, (writeW_outside _ base _ (by decide)).word (Or.inl (by decide)) (by decide), m3, m2,
      word_writeW_self, e1]
  · rw [mt, word_writeW_self, e3]
  · intro x hx
    rw [mt, writeW_outside _ base _ (by decide) x (by simp only [CNT, PCUR] at hx ⊢; omega), m3, m2,
      writeW_outside _ base _ (by decide) x (by simp only [PCUR] at hx ⊢; omega), m1]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [gt, g3 r hr.2, g2, g1 r hr.1]

theorem vnext_eq : ([.mov .rsi (.mem (sc PPK)), .store (sc PCUR) .rsi, .mov .rbx (.mem (sc CNT)),
    .alu .sub .rbx (.imm 1), .store (sc CNT) .rbx] : List Instr) = ([.mov .rsi (.mem (sc PPK))] : List Instr) ++
    (([.store (sc PCUR) .rsi] : List Instr) ++ (([.mov .rbx (.mem (sc CNT))] : List Instr) ++
    (([.alu .sub .rbx (.imm 1)] : List Instr) ++ ([.store (sc CNT) .rbx] : List Instr)))) := rfl

/-- The loop's pointer at `A`, and its count moved down. -/
theorem vnext_ok {s : State} {base : Addr} (hs : Scr s base) {k : Nat} (hk : k < 2)
    (hc : word s.mem base CNT = BitVec.ofNat 64 (k + 1)) :
    WP isa (.block ([.mov .rsi (.mem (sc PPK)), .store (sc PCUR) .rsi, .mov .rbx (.mem (sc CNT)),
      .alu .sub .rbx (.imm 1), .store (sc CNT) .rbx] : List Instr)) s fun t =>
      word t.mem base PCUR = word s.mem base PPK ∧ word t.mem base CNT = BitVec.ofNat 64 k ∧
      t.zf = some (decide (k = 0)) ∧ Outside base PCUR 16 s.mem t.mem ∧
      (∀ r, r ∉ [Reg.rsi, .rbx] → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  rw [vnext_eq, WP.block_append_iff]
  refine WP.mono (movMem_ok hs .rsi (d := PPK) (by decide)) fun s1 ⟨e1, g1, m1, rd1, wr1⟩ => ?_
  have hs1 : Scr s1 base := ⟨(g1 _ (by decide)).trans hs.rdi, wr1 ▸ hs.wr, hs.nowrap⟩
  rw [WP.block_append_iff]
  refine WP.mono (storeZ_ok hs1 .rsi (d := PCUR) (by decide)) fun s2 ⟨m2, g2, rd2, wr2, _⟩ => ?_
  have hs2 : Scr s2 base := ⟨by rw [g2]; exact hs1.rdi, wr2 ▸ hs1.wr, hs.nowrap⟩
  rw [WP.block_append_iff]
  refine WP.mono (movMem_ok hs2 .rbx (d := CNT) (by decide)) fun s3 ⟨e3, g3, m3, rd3, wr3⟩ => ?_
  have hs3 : Scr s3 base := ⟨(g3 _ (by decide)).trans hs2.rdi, wr3 ▸ hs2.wr, hs.nowrap⟩
  have c3 : s3.gpr .rbx = BitVec.ofNat 64 (k + 1) := by
    rw [e3, m2, (writeW_outside _ base _ (by decide)).word (Or.inr (by decide)) (by decide), m1, hc]
  rw [WP.block_append_iff]
  refine WP.mono (Proof.X448.X86_64.decRbx_ok (by omega) c3) fun s4 ⟨e4, g4, m4, rd4, wr4, z4⟩ => ?_
  have hs4 : Scr s4 base := ⟨(g4 _ (by decide)).trans hs3.rdi, wr4 ▸ hs3.wr, hs.nowrap⟩
  refine WP.mono (storeZ_ok hs4 .rbx (d := CNT) (by decide)) fun t ⟨mt, gt, rdt, wrt, zt⟩ =>
    ⟨?_, ?_, by rw [zt, z4], ?_, fun r hr => ?_, by rw [rdt, rd4, rd3, rd2, rd1],
      by rw [wrt, wr4, wr3, wr2, wr1]⟩
  · rw [mt, (writeW_outside _ base _ (by decide)).word (Or.inl (by decide)) (by decide), m4, m3, m2,
      word_writeW_self, e1]
  · rw [mt, word_writeW_self, e4]
  · intro x hx
    rw [mt, writeW_outside _ base _ (by decide) x (by simp only [CNT, PCUR] at hx ⊢; omega), m4, m3, m2,
      writeW_outside _ base _ (by decide) x (by simp only [PCUR] at hx ⊢; omega), m1]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [gt, g4 r hr.2, g3 r hr.2, g2, g1 r hr.1]

theorem vdecodeBody_eq (F : Impl.X448.X86_64.Field) (rt : Prog isa) : vdecodeBody F rt =
    .seq (.block (copyOut RX (slot 6) ++ (copyOut RY (slot 7) ++ (consts ++
      ([.mov .rsi (.mem (sc PCUR))] : List Instr))))) (.seq (decode F 6 7 rt)
      (.block ([.mov .rsi (.mem (sc PPK)), .store (sc PCUR) .rsi, .mov .rbx (.mem (sc CNT)),
        .alu .sub .rbx (.imm 1), .store (sc CNT) .rbx] : List Instr))) := by
  simp only [vdecodeBody, List.append_assoc]

include hf in
/-- One decoding: of the point at `q` (`PCUR`), into slots 6 and 7, with their old values kept
at `RX` and `RY`; then `PCUR` at `A`, and the count moved down. -/
theorem vdecodeBody_ok (hR : RecoverOk) {rt : Prog isa} (hrt : RootOk rt) {s : State} {base q : Addr}
    (hs : Scr s base) {k : Nat}
    (hk : k < 2) (hq : word s.mem base PCUR = q) (hc : word s.mem base CNT = BitVec.ofNat 64 (k + 1))
    (hr8 : ∀ i < 7, InRegions (s.rd ++ s.wr) (q + BitVec.ofNat 64 (8 * i)) 8)
    (hr56 : InRegions (s.rd ++ s.wr) (q + BitVec.ofNat 64 56) 1)
    (hfar : ∀ i < 57, 8192 ≤ ofs base (q + BitVec.ofNat 64 i)) :
    WP isa (vdecodeBody fld rt) s fun t =>
      word t.mem base PCUR = word s.mem base PPK ∧ word t.mem base CNT = BitVec.ofNat 64 k ∧
      t.zf = some (decide (k = 0)) ∧
      F t.mem base RX = E s.mem base 6 ∧ F t.mem base RY = E s.mem base 7 ∧
      (∃ c : BitVec 64, (c = 0 ↔ (Spec.Ed448.decodePoint (Spec.Ed448.bytesAt s.mem q 57)).isSome) ∧
        word t.mem base BAD = word s.mem base BAD ||| c) ∧
      (∀ a, Spec.Ed448.decodePoint (Spec.Ed448.bytesAt s.mem q 57) = some a →
        E t.mem base 6 = a.X ∧ E t.mem base 7 = a.Y ∧ a.Z = 1) ∧
      (∀ r, r ∉ .rbx :: .rsi :: clob → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      DFrame base s.mem t.mem := by
  have hWc : ∀ r, r ∉ .rbx :: .rsi :: clob → r ∉ W := fun r hr h => hr (by
    have : ∀ x ∈ W, x ∈ clob := by decide
    exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (this r h)))
  rw [vdecodeBody_eq]
  apply WP.seq
  rw [WP.block_append_iff]
  refine WP.mono (copyOut_ok hs (o := RX) (a := slot 6) (by decide) (by decide))
    fun s1 ⟨f1, o1, g1, rd1, wr1⟩ => ?_
  have hs1 : Scr s1 base := ⟨(g1 _ (by decide)).trans hs.rdi, wr1 ▸ hs.wr, hs.nowrap⟩
  rw [WP.block_append_iff]
  refine WP.mono (copyOut_ok hs1 (o := RY) (a := slot 7) (by decide) (by decide))
    fun s2 ⟨f2, o2, g2, rd2, wr2⟩ => ?_
  have hs2 : Scr s2 base := ⟨(g2 _ (by decide)).trans hs1.rdi, wr2 ▸ hs1.wr, hs.nowrap⟩
  rw [WP.block_append_iff]
  refine WP.mono (consts_ok hs2) fun s3 ⟨_, q3, d3, o3, g3, rd3, wr3, _⟩ => ?_
  have hs3 : Scr s3 base := ⟨(g3 _ (by decide)).trans hs2.rdi, wr3 ▸ hs2.wr, hs.nowrap⟩
  refine WP.mono (movMem_ok hs3 .rsi (d := PCUR) (by decide)) fun s4 ⟨si4, g4, m4, rd4, wr4⟩ => ?_
  have hs4 : Scr s4 base := ⟨(g4 _ (by decide)).trans hs3.rdi, wr4 ▸ hs3.wr, hs.nowrap⟩
  have w3 : ∀ d, d + 8 ≤ 8192 → (d + 8 ≤ RX ∨ RY + 56 ≤ d) → 64 + 1584 ≤ d →
      word s3.mem base d = word s.mem base d := fun d h1 h2 h3 => by
    simp only [RX, RY] at h2
    rw [o3.word (Or.inr h3) (by omega), o2.word (by simp only [RY]; omega) (by omega),
      o1.word (by simp only [RX]; omega) (by omega)]
  have hp4 : s4.gpr .rsi = q := by
    rw [si4, w3 PCUR (by decide) (Or.inr (by decide)) (by decide), hq]
  have O4 : Outside base 0 8192 s.mem s4.mem := by
    rw [m4]
    exact ((o1.mono (by decide) (by decide)).trans (o2.mono (by decide) (by decide))).trans
      (o3.mono (by decide) (by decide))
  have rr4 : s4.rd ++ s4.wr = s.rd ++ s.wr := by rw [rd4, wr4, rd3, wr3, rd2, wr2, rd1, wr1]
  have h10 : E s4.mem base 10 = 1 := by rw [m4]; exact (congrArg Spec.Ed448.Point.Z q3 :)
  have h11 : E s4.mem base 11 = Spec.Ed448.d := by rw [m4]; exact d3
  apply WP.seq
  refine WP.mono (decode_ok hf hR hrt hs4 hp4 6 7 (Or.inl ⟨rfl, rfl⟩) h10 h11 (by rw [rr4]; exact hr8)
    (by rw [rr4]; exact hr56) hfar) fun s5 ⟨⟨c, hc5, b5⟩, v5, _, g5, rd5, wr5, o5⟩ => ?_
  rw [far_bytes O4 hfar] at hc5 v5
  have hs5 : Scr s5 base := ⟨(g5 _ (by decide)).trans hs4.rdi, wr5 ▸ hs4.wr, hs.nowrap⟩
  refine WP.mono (vnext_ok hs5 hk (by
    rw [o5.word (Or.inr (by decide)) (Or.inr (by decide)) (by decide),
      m4, w3 CNT (by decide) (Or.inr (by decide)) (by decide), hc]))
    fun t ⟨pt', ct, zt, ot, gt, rdt, wrt⟩ => ?_
  refine ⟨?_, ct, zt, ?_, ?_, ⟨c, hc5, ?_⟩, fun a ha => ?_, fun r hr => ?_, by rw [rdt, rd5, rd4,
    rd3, rd2, rd1], by rw [wrt, wr5, wr4, wr3, wr2, wr1], ?_⟩
  · rw [pt', o5.word (Or.inr (by decide)) (Or.inl (by decide)) (by decide),
      m4, w3 PPK (by decide) (Or.inl (by decide)) (by decide)]
  · show VG.Proof.X448.toFe (fe t.mem base RX) = VG.Proof.X448.toFe (fe s.mem base (slot 6))
    rw [ot.fe (Or.inl (by decide)) (by decide), (show fe s5.mem base RX = fe s4.mem base RX from
        o5.mv (Or.inr (by decide)) (Or.inr (by decide)) (by decide)),
      m4, o3.fe (Or.inr (by decide)) (by decide), o2.fe (Or.inl (by decide)) (by decide), f1]
  · show VG.Proof.X448.toFe (fe t.mem base RY) = VG.Proof.X448.toFe (fe s.mem base (slot 7))
    rw [ot.fe (Or.inl (by decide)) (by decide), (show fe s5.mem base RY = fe s4.mem base RY from
        o5.mv (Or.inr (by decide)) (Or.inr (by decide)) (by decide)),
      m4, o3.fe (Or.inr (by decide)) (by decide), f2, o1.fe (Or.inl (by decide)) (by decide)]
  · rw [ot.word (Or.inl (by decide)) (by decide), b5, m4, w3 BAD (by decide) (Or.inl (by decide)) (by decide)]
  · obtain ⟨vx, vy, vz⟩ := v5 a ha
    exact ⟨by rw [E_outside ot 6 (Or.inl (by decide)), vx], by rw [E_outside ot 7 (Or.inl (by decide)), vy], vz⟩
  · simp only [List.mem_cons, not_or] at hr
    rw [gt r (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; exact ⟨hr.2.1, hr.1⟩),
      g5 r (by simp only [List.mem_cons, not_or]; exact ⟨hr.1, hr.2.2⟩), g4 r hr.2.1,
      g3 r (hWc r (by simp only [List.mem_cons, not_or]; exact hr)),
      g2 r (hWc r (by simp only [List.mem_cons, not_or]; exact hr)),
      g1 r (hWc r (by simp only [List.mem_cons, not_or]; exact hr))]
  · rw [m4] at o5
    exact ((((DFrame.of1 o1 (by decide) (by decide)).trans (DFrame.of1 o2 (by decide) (by decide))).trans
      (o3.left _ _)).trans (DFrame.of2 o5)).trans (DFrame.of1 ot (by decide) (by decide))

include hf in
/-- `R` (at `sig`) decoded and kept at `RX` and `RY`, then `A` (at `pk`) into slots 6 and 7. -/
theorem vdecode_ok (hR : RecoverOk) {rt : Prog isa} (hrt : RootOk rt) {s : State} {base pk sig : Addr}
    (hs : Scr s base)
    (hpk : word s.mem base PPK = pk) (hsig : word s.mem base PSIG = sig)
    (rp : ∀ i n, i + n ≤ 57 → InRegions (s.rd ++ s.wr) (pk + BitVec.ofNat 64 i) n)
    (rs : ∀ i n, i + n ≤ 57 → InRegions (s.rd ++ s.wr) (sig + BitVec.ofNat 64 i) n)
    (fp : ∀ i < 57, 8192 ≤ ofs base (pk + BitVec.ofNat 64 i))
    (fs : ∀ i < 57, 8192 ≤ ofs base (sig + BitVec.ofNat 64 i)) :
    WP isa (vdecode fld rt) s fun t =>
      (∃ cR cA : BitVec 64,
        (cR = 0 ↔ (Spec.Ed448.decodePoint (Spec.Ed448.bytesAt s.mem sig 57)).isSome) ∧
        (cA = 0 ↔ (Spec.Ed448.decodePoint (Spec.Ed448.bytesAt s.mem pk 57)).isSome) ∧
        word t.mem base BAD = word s.mem base BAD ||| cR ||| cA) ∧
      (∀ r, Spec.Ed448.decodePoint (Spec.Ed448.bytesAt s.mem sig 57) = some r →
        F t.mem base RX = r.X ∧ F t.mem base RY = r.Y ∧ r.Z = 1) ∧
      (∀ a, Spec.Ed448.decodePoint (Spec.Ed448.bytesAt s.mem pk 57) = some a →
        E t.mem base 6 = a.X ∧ E t.mem base 7 = a.Y ∧ a.Z = 1) ∧
      (∀ r, r ∉ .rbx :: .rsi :: clob → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      DFrame base s.mem t.mem := by
  rw [vdecode]
  apply WP.seq
  refine WP.mono (vdecodeInit_ok hs) fun s1 ⟨pc1, cn1, o1, g1, rd1, wr1⟩ => ?_
  refine WP.loop (M := isa) (fun m (t : State) => 1 ≤ m ∧ m ≤ 2 ∧
      word t.mem base PCUR = (if m = 2 then sig else pk) ∧ word t.mem base CNT = BitVec.ofNat 64 m ∧
      (∀ r, r ∉ .rbx :: .rsi :: clob → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      DFrame base s.mem t.mem ∧ (m = 2 → word t.mem base BAD = word s.mem base BAD) ∧
      (m = 1 → (∃ cR : BitVec 64,
          (cR = 0 ↔ (Spec.Ed448.decodePoint (Spec.Ed448.bytesAt s.mem sig 57)).isSome) ∧
          word t.mem base BAD = word s.mem base BAD ||| cR) ∧
        ∀ r, Spec.Ed448.decodePoint (Spec.Ed448.bytesAt s.mem sig 57) = some r →
          E t.mem base 6 = r.X ∧ E t.mem base 7 = r.Y ∧ r.Z = 1))
    ?_ 2 s1 ⟨by decide, by decide, by rw [pc1, hsig]; rfl, cn1, fun r hr => g1 r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr ⊢; exact ⟨hr.2.1, hr.1⟩),
      rd1, wr1, DFrame.of1 o1 (by decide) (by decide),
      fun _ => o1.word (Or.inl (by decide)) (by decide), fun h => absurd h (by decide)⟩
  intro m t ⟨h1, h2, pct, cnt, gt, rdt, wrt, Dt, b2, b1⟩
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  have ht : Scr t base := ⟨(gt _ (by decide)).trans hs.rdi, wrt ▸ hs.wr, hs.nowrap⟩
  have rrt : t.rd ++ t.wr = s.rd ++ s.wr := by rw [rdt, wrt]
  have Ot : Outside base 0 8192 s.mem t.mem := Dt.wide.mono (by decide) (by decide)
  have wpk : word t.mem base PPK = pk := by
    rw [Outside2.word Dt (Or.inr (by decide)) (Or.inl (by decide)) (by decide), hpk]
  rcases (show k = 0 ∨ k = 1 by omega) with rfl | rfl
  · obtain ⟨⟨cR, hcR, bt⟩, vt⟩ := b1 rfl
    refine WP.mono (vdecodeBody_ok hf hR hrt ht (k := 0) (by decide) (by rw [pct]; rfl) cnt
      (fun i hi => by rw [rrt]; exact rp _ _ (by omega)) (by rw [rrt]; exact rp _ _ (by omega)) fp)
      fun u ⟨_, _, zu, fx, fy, ⟨c, hc, bu⟩, vu, gu, rdu, wru, Du⟩ => ?_
    rw [far_bytes Ot fp] at hc vu
    simp only [eval, zu, Option.map_some]
    refine .inl ⟨rfl, ⟨cR, c, hcR, hc, by rw [bu, bt]⟩, fun r hr => ?_, vu,
      fun r hr => (gu r hr).trans (gt r hr), rdu.trans rdt, wru.trans wrt, Dt.trans Du⟩
    obtain ⟨x, y, z⟩ := vt r hr
    exact ⟨by rw [fx, x], by rw [fy, y], z⟩
  · refine WP.mono (vdecodeBody_ok hf hR hrt ht (k := 1) (by decide) (by rw [pct]; rfl) cnt
      (fun i hi => by rw [rrt]; exact rs _ _ (by omega)) (by rw [rrt]; exact rs _ _ (by omega)) fs)
      fun u ⟨pcu, cnu, zu, _, _, ⟨c, hc, bu⟩, vu, gu, rdu, wru, Du⟩ => ?_
    rw [far_bytes Ot fs] at hc vu
    simp only [eval, zu, Option.map_some]
    exact .inr ⟨rfl, 1, by omega, by decide, by decide, by rw [pcu, wpk]; rfl, cnu,
      fun r hr => (gu r hr).trans (gt r hr), rdu.trans rdt, wru.trans wrt, Dt.trans Du,
      fun h => absurd h (by decide), fun _ => ⟨⟨c, hc, by rw [bu, b2 rfl]⟩, vu⟩⟩

include hf in
/-- `A` negated (slot 6), with `Q` the neutral point, `B` and `d`. -/
theorem vnegA_ok {s : State} {base : Addr} (hs : Scr s base) :
    WP isa (.block (vnegA fld)) s fun t =>
      E t.mem base 6 = 0 - E s.mem base 6 ∧ E t.mem base 7 = E s.mem base 7 ∧ E t.mem base 10 = 1 ∧
      pt (E t.mem base) 0 1 2 = Spec.Ed448.identity ∧ pt (E t.mem base) 8 9 10 = Spec.Ed448.basePoint ∧
      E t.mem base 11 = Spec.Ed448.d ∧
      (∀ r, r ∉ clob → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      Outside base 64 1584 s.mem t.mem := by
  rw [vnegA, WP.block_append_iff]
  refine WP.mono (consts_ok hs) fun s4 ⟨p4, q4, d4, o4, g4, rd4, wr4, k4⟩ => ?_
  have hs4 : Scr s4 base := ⟨(g4 _ (by decide)).trans hs.rdi, wr4 ▸ hs.wr, hs.nowrap⟩
  refine WP.mono (fieldCode_ok hf [.sub 6 0 6] (by decide) hs4) fun t ⟨kt, et⟩ => ?_
  have keep : ∀ i : Index, i ≠ 6 → E t.mem base i = E s4.mem base i := fun i hi => by
    rw [et]; exact evalOps_keep _ _ _ fun op hop => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hop
      subst hop; exact fun h => hi (Fin.ext (by simp only [fopDest] at h; omega))
  have t6 : E t.mem base 6 = E s4.mem base 0 - E s4.mem base 6 := by rw [et]; rfl
  have hW : ∀ x ∈ W, x ∈ clob := by decide
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, fun r hr => ?_, kt.rd.trans rd4, kt.wr.trans wr4,
    fun x hx => by rw [kt.mem x hx, o4 x hx]⟩
  · rw [t6, show E s4.mem base 0 = 0 from (congrArg Spec.Ed448.Point.X p4 :), k4 6 (by decide) (by decide)]
  · rw [keep 7 (by decide), k4 7 (by decide) (by decide)]
  · rw [keep 10 (by decide)]; exact (congrArg Spec.Ed448.Point.Z q4 :)
  · rw [pt_congr (keep 0 (by decide)) (keep 1 (by decide)) (keep 2 (by decide)), p4]
  · rw [pt_congr (keep 8 (by decide)) (keep 9 (by decide)) (keep 10 (by decide)), q4]
  · rw [keep 11 (by decide), d4]
  · rw [kt.gpr r hr, g4 r (fun h => hr (hW r h))]

/-- Two stages' bound on what they write, as one range. -/
theorem wide {base : Addr} {m m' : Mem} (h : Outside2 base 64 1584 BAD 80 m m') :
    Outside base 64 1704 m m' :=
  h.outside (by decide) (by decide) (by decide) (by decide)

include hf hP in
theorem verifyEquation_correct (hR : RecoverOk) (hE : VerifyEqOk) {rt : Prog isa} (hrt : RootOk rt)
    {s : State} (hp : verifyEquationLocal.pre s) :
    WP isa (verifyEquationWith fld P rt) s fun t => gprPreserved s t ∧ verifyEquationLocal.post s t := by
  obtain ⟨hr, hw, hdk, hds, hdc, hret, hn⟩ := hp
  obtain ⟨base, hbase⟩ : ∃ b, s.gpr .rcx = b := ⟨_, rfl⟩
  rw [hbase] at hdk hds hdc hret hn hw
  have hws : (⟨base, 8192⟩ : Region) ∈ s.wr := by rw [hw]; simp
  have rpk : ∀ i n, i + n ≤ 57 → InRegions (s.rd ++ s.wr) (s.gpr .rdi + BitVec.ofNat 64 i) n :=
    fun i n h => ⟨⟨s.gpr .rdi, 57⟩, by rw [hr]; simp,
      Offset.contains_base _ (d := i) (n := n) (k := 57) h (by omega)⟩
  have rsg : ∀ i n, i + n ≤ 114 → InRegions (s.rd ++ s.wr) (s.gpr .rsi + BitVec.ofNat 64 i) n :=
    fun i n h => ⟨⟨s.gpr .rsi, 114⟩, by rw [hr]; simp,
      Offset.contains_base _ (d := i) (n := n) (k := 114) h (by omega)⟩
  have rch : ∀ i n, i + n ≤ 57 → InRegions (s.rd ++ s.wr) (s.gpr .rdx + BitVec.ofNat 64 i) n :=
    fun i n h => ⟨⟨s.gpr .rdx, 57⟩, by rw [hr]; simp,
      Offset.contains_base _ (d := i) (n := n) (k := 57) h (by omega)⟩
  have fpk : ∀ i < 57, 8192 ≤ ofs base (s.gpr .rdi + BitVec.ofNat 64 i) := fun i hi => far hdk hi (by decide)
  have fsg : ∀ i < 57, 8192 ≤ ofs base (s.gpr .rsi + BitVec.ofNat 64 i) :=
    fun i hi => far hds (by omega) (by decide)
  have fs : ∀ i < 57, 8192 ≤ ofs base (s.gpr .rsi + BitVec.ofNat 64 57 + BitVec.ofNat 64 i) :=
    fun i hi => by rw [Offset.add_add]; exact far hds (by omega) (by decide)
  have fch : ∀ i < 57, 8192 ≤ ofs base (s.gpr .rdx + BitVec.ofNat 64 i) := fun i hi => far hdc hi (by decide)
  obtain ⟨S, hS⟩ : ∃ S, Spec.Ed448.decodeLE (Spec.Ed448.bytesAt s.mem (s.gpr .rsi + BitVec.ofNat 64 57) 57) = S :=
    ⟨_, rfl⟩
  obtain ⟨K, hK⟩ : ∃ K, Spec.Ed448.decodeLE (Spec.Ed448.bytesAt s.mem (s.gpr .rdx) 57) = K := ⟨_, rfl⟩
  rw [verifyEquationWith]
  -- The entry: the callee-saved registers saved, and the pointers.
  apply WP.seq
  refine WP.mono (ventry_ok hbase hws hn) fun s1 ⟨hs1, sv1, r81, r91, si1, g1, o1, rd1, wr1⟩ => ?_
  have rr1 : s1.rd ++ s1.wr = s.rd ++ s.wr := by rw [rd1, wr1]
  have O1 : Outside base 0 8192 s.mem s1.mem := o1.mono (by decide) (by decide)
  -- The bits of `k` and `S`.
  apply WP.seq
  refine WP.mono (vbits_ok (sig := s.gpr .rsi) (ch := s.gpr .rdx) hs1 si1 r91
    (fun q hq => by rw [rr1, Offset.add_add]; exact rsg _ _ (by omega))
    (fun q hq => by rw [rr1]; exact rch _ _ (by omega)) fs fch)
    fun s2 ⟨bs2, bk2, si2, g2, rd2, wr2, o2⟩ => ?_
  rw [far_bytes O1 fs, hS] at bs2
  rw [far_bytes O1 fch, hK] at bk2
  have hs2 : Scr s2 base := ⟨(g2 _ (by decide)).trans hs1.rdi, wr2 ▸ hs1.wr, hn⟩
  have rr2 : s2.rd ++ s2.wr = s.rd ++ s.wr := by rw [rd2, wr2, rd1, wr1]
  have O2 : Outside base 0 8192 s.mem s2.mem := O1.trans (o2.mono (by decide) (by decide))
  -- The pointers saved, and the check of `S`.
  apply WP.seq
  refine WP.mono (vstart_ok (pk := s.gpr .rdi) (sig := s.gpr .rsi) hs2 (by rw [g2 _ (by decide), r81]) (by rw [g2 _ (by decide), r91]) si2
    (fun i hi => by rw [rr2, Offset.add_add]; exact rsg _ _ (by omega))
    (by rw [rr2, Offset.add_add]; exact rsg _ _ (by omega)) fs)
    fun s3 ⟨pk3, sig3, ⟨c0, hc0, b3⟩, g3, rd3, wr3, o3⟩ => ?_
  rw [far_bytes O2 fs, hS] at hc0
  have hs3 : Scr s3 base := ⟨(g3 _ (by decide)).trans hs2.rdi, wr3 ▸ hs2.wr, hn⟩
  have rr3 : s3.rd ++ s3.wr = s.rd ++ s.wr := by rw [rd3, wr3, rr2]
  have O3 : Outside base 0 8192 s.mem s3.mem := O2.trans (o3.mono (by decide) (by decide))
  -- `R` and `A`, decoded by one loop.
  apply WP.seq
  refine WP.mono (vdecode_ok hf hR hrt hs3 pk3 sig3 (fun i n h => by rw [rr3]; exact rpk i n h)
    (fun i n h => by rw [rr3]; exact rsg i n (by omega)) fpk fsg)
    fun s4 ⟨⟨cR, cA, hcR, hcA, b4⟩, vr4, va4, g4, rd4, wr4, D4⟩ => ?_
  rw [far_bytes O3 fpk] at hcA va4
  rw [far_bytes O3 fsg, ← bytesAt_take57] at hcR vr4
  have hs4 : Scr s4 base := ⟨(g4 _ (by decide)).trans hs3.rdi, wr4 ▸ hs3.wr, hn⟩
  have O4 : Outside base 0 8192 s.mem s4.mem := O3.trans (D4.wide.mono (by decide) (by decide))
  -- `A` negated, and the constants.
  apply WP.seq
  refine WP.mono (vnegA_ok hf hs4) fun s4' ⟨n6, n7, n10, p4, q4, d4, g4', rd4', wr4', o4⟩ => ?_
  have hs4' : Scr s4' base := ⟨(g4' _ (by decide)).trans hs4.rdi, wr4' ▸ hs4.wr, hn⟩
  have na4 : ∀ a, Spec.Ed448.decodePoint (Spec.Ed448.bytesAt s.mem (s.gpr .rdi) 57) = some a →
      pt (E s4'.mem base) 6 7 10 = negPoint a := fun a ha => by
    obtain ⟨vx, vy, vz⟩ := va4 a ha
    show (⟨E s4'.mem base 6, E s4'.mem base 7, E s4'.mem base 10⟩ : Spec.Ed448.Point) = ⟨0 - a.X, a.Y, a.Z⟩
    rw [n6, n7, n10, vx, vy, vz]
  -- The loop.
  apply WP.seq
  rw [vloop]
  apply WP.seq
  refine WP.mono (show WP isa (.block [.mov32 .rbx (.imm (BitVec.ofNat 32 456))]) s4' _ from
    Proof.X448.X86_64.setRbx_ok s4' 456 (by decide)) fun s5 ⟨rbx5, g5, m5, rd5, wr5⟩ => ?_
  have hs5 : Scr s5 base := ⟨(g5 _ (by decide)).trans hs4'.rdi, wr5 ▸ hs4'.wr, hn⟩
  have bits5 : ∀ o : Nat, o + 456 ≤ 8192 → 2048 ≤ o → ∀ t < 456,
      s5.mem (off base (o + t)) = s2.mem (off base (o + t)) := fun o ho1 ho2 t ht => by
    have hofs := VG.Proof.X448.X86_64.ofs_off' base (d := o + t) (by omega)
    rw [m5, o4 _ (Or.inr (by rw [hofs]; omega)), D4.wide _ (Or.inr (by rw [hofs]; omega)),
      o3 _ (Or.inr (by rw [hofs]; simp only [KC]; omega))]
  have I5 : VInv base S K (pt (E s5.mem base) 6 7 10) s5 456 s5 := by
    refine ⟨hs5, rbx5, fun _ _ => rfl, rfl, rfl, Outside.refl _ _ _ _, ?_, rfl, ?_, ?_⟩
    · rw [m5]; exact q4
    · rw [m5]; exact d4
    · rw [Nat.sub_self, m5, p4]; rfl
  refine WP.mono (vloop_ok hP (fun t ht => by rw [bits5 BITS (by decide) (by decide) t ht]; exact bs2 t ht)
    (fun t ht => by rw [bits5 KBITS (by decide) (by decide) t ht]; exact bk2 t ht)
    456 s5 (by decide) (by decide) I5) fun s6 I6 => ?_
  have M6 : Outside base 64 1584 s4'.mem s6.mem := by
    have h6 := I6.mem
    rw [m5] at h6
    exact h6
  have O7 : Outside base 0 8192 s.mem s6.mem :=
    (O4.trans (o4.mono (by decide) (by decide))).trans (M6.mono (by decide) (by decide))
  have sv7 : Saved base s.gpr s6.mem :=
    ((((sv1.outside o2 (by decide)).outside o3 (by decide)).outside D4.wide (by decide)).outside o4
      (by decide)).outside M6 (by decide)
  -- `[4]Q` and `[4]R` compared, and the result.
  refine WP.mono (vfinish_ok hf hP I6.scr sv7) fun t ⟨at', rt, gt, rdt, wrt, ot⟩ => ?_
  have hBAD : word s6.mem base BAD = c0 ||| cR ||| cA := by
    rw [M6.word (Or.inr (by decide)) (by decide),
      o4.word (Or.inr (by decide)) (by decide), b4, b3]
  have OT : Outside base 0 8192 s.mem t.mem := O7.trans ((wide ot).mono (by decide) (by decide))
  refine ⟨⟨fun r hr => ?_, ?_⟩, ?_⟩
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact rt (.rbx, 0) (by decide)
    · exact rt (.rbp, 8) (by decide)
    · rw [gt _ (by decide), I6.gpr _ (by decide), g5 _ (by decide), g4' _ (by decide),
        g4 _ (by decide), g3 _ (by decide), g2 _ (by decide), g1 _ (by decide)]
    · exact rt (.r12, 16) (by decide)
    · exact rt (.r13, 24) (by decide)
    · exact rt (.r14, 32) (by decide)
    · exact rt (.r15, 40) (by decide)
  · exact (VG.Proof.Ed448.X86_64.Outside.frame OT).readW (r := ⟨s.gpr .rsp, 8⟩)
      (Region.contains_self _ _) (by
        simp only [List.mem_cons, List.not_mem_nil, or_false]
        rintro r rfl; exact hret) (by decide)
  · show t.gpr .rax = _
    rw [at']
    refine if_congr ?_ rfl rfl
    rw [hBAD, or_eq_zero64, or_eq_zero64]
    cases ha : Spec.Ed448.decodePoint (Spec.Ed448.bytesAt s.mem (s.gpr .rdi) 57) with
    | none =>
      rw [verifyEquation_none (Or.inl ha)]
      refine ⟨fun h => absurd (hcA.mp h.1.2) (by rw [ha]; decide), fun h => absurd h (by decide)⟩
    | some a =>
      cases hR : Spec.Ed448.decodePoint ((Spec.Ed448.bytesAt s.mem (s.gpr .rsi) 114).take 57) with
      | none =>
        rw [verifyEquation_none (Or.inr hR)]
        refine ⟨fun h => absurd (hcR.mp h.1.1.2) (by rw [hR]; decide), fun h => absurd h (by decide)⟩
      | some r =>
        have cA0 : cA = 0 := hcA.mpr (by rw [ha]; rfl)
        have cR0 : cR = 0 := hcR.mpr (by rw [hR]; rfl)
        have hA : pt (E s5.mem base) 6 7 10 = negPoint a := by rw [m5]; exact na4 a ha
        have hQ : pt (E s6.mem base) 0 1 2 = vladder (Spec.Ed448.decodeLE
            ((Spec.Ed448.bytesAt s.mem (s.gpr .rsi) 114).drop 57))
            (Spec.Ed448.decodeLE (Spec.Ed448.bytesAt s.mem (s.gpr .rdx) 57)) (negPoint a) 456 := by
          have := I6.rep
          rw [Nat.sub_zero, hA] at this
          rw [bytesAt_drop57, hS, hK]
          exact this
        have hRR : (⟨F s6.mem base RX, F s6.mem base RY, 1⟩ : Spec.Ed448.Point) = r := by
          obtain ⟨vx, vy, vz⟩ := vr4 r hR
          have fx : F s6.mem base RX = F s4.mem base RX := by
            show VG.Proof.X448.toFe (fe s6.mem base RX) = VG.Proof.X448.toFe (fe s4.mem base RX)
            rw [M6.fe (Or.inr (by decide)) (by decide), o4.fe (Or.inr (by decide)) (by decide)]
          have fy : F s6.mem base RY = F s4.mem base RY := by
            show VG.Proof.X448.toFe (fe s6.mem base RY) = VG.Proof.X448.toFe (fe s4.mem base RY)
            rw [M6.fe (Or.inr (by decide)) (by decide), o4.fe (Or.inr (by decide)) (by decide)]
          rw [fx, fy, vx, vy, ← vz]
        rw [hE _ _ _ _ _ (bytesAt57_len _ _) (bytesAt114_len _ _) (bytesAt57_len _ _) ha hR, ← hQ, ← hRR,
          Bool.and_eq_true, decide_eq_true_iff, bytesAt_drop57, hS, cA0, cR0, hc0]
        exact ⟨fun h => ⟨h.1.1.1, h.2⟩, fun h => ⟨⟨⟨h.1, rfl⟩, rfl⟩, h.2⟩⟩

theorem verifyEquation_inline : verifyEquation.inline =
    verifyEquationWith Impl.X448.X86_64.baseline Point64.bodies (rootCall Impl.X448.X86_64.baseline).inline := rfl

/-- `vg_ed448_verify_equation`, its calls of the point functions and `vg_gf448_r64_pow223`
inlined. -/
theorem verifyEquation_correct_inline (hR : RecoverOk) (hE : VerifyEqOk) {s : State}
    (hp : verifyEquationLocal.pre s) :
    WP isa verifyEquation.inline s fun t => gprPreserved s t ∧ verifyEquationLocal.post s t := by
  rw [verifyEquation_inline]
  exact verifyEquation_correct Proof.X448.X86_64.baseline_ok Point64.bodies_ok hR hE (rootCall_ok Proof.X448.X86_64.baseline_ok) hp

end VG.Proof.Ed448.X86_64
