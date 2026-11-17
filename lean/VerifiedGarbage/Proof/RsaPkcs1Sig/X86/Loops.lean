module

public import VerifiedGarbage.Proof.Framework.WriteBytes
public import VerifiedGarbage.Impl.Bignum.X86.PublicFn
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.TCB.X86.Isa
public import VerifiedGarbage.Proof.Framework.X86.Wp
import VerifiedGarbage.Proof.Mont.X86.Instr
public import VerifiedGarbage.Impl.Mont.Mod
public import VerifiedGarbage.Proof.Framework.X86.Exec

/-! ### `RsaPkcs1Sig.X86.Instr`, which this module and modules that import it used -/

section

/-!
# The x86 RSA padding functions: instruction rules

Continuation-passing rules (as `Proof/Framework/X86/Wp.lean`) for the byte
loads and stores of the padding functions (`movzx8`, `store8`), and the
operands they read (`readSrc`): a register, an immediate, or a word of
memory; with the rules of `Proof/Mont/X86/Instr.lean` for any operand.
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Sig.X86

open VG VG.X86 VG.X86.Wp

section
variable {is : List Instr} {s : State} {Q : State → Prop}

theorem wp_movzx8 {d : Reg} {m : MemOp} {a : Addr} (ha : s.ea m = a) (hin : InRegions (s.rd ++ s.wr) a 1)
    (k : ∀ s', Upd s s' d ((s.mem a).setWidth 32) → WP isa (.block is) s' Q) :
    WP isa (.block (.movzx8 d m :: is)) s Q := by
  refine cons (s' := s.setReg d ((s.mem a).setWidth 32)) ?_ (k _ (Upd.setReg _ _ _))
  simp [exec, State.load8, ha, hin]

theorem wp_store8 {m : MemOp} {r : Reg8} {a : Addr} (ha : s.ea m = a) (hout : InRegions s.wr a 1)
    (k : ∀ s', Mupd s s' (s.mem.writeW a ((s.gpr r.reg).setWidth 8)) → WP isa (.block is) s' Q) :
    WP isa (.block (.store8 m r :: is)) s Q := by
  refine cons (s' := { s with mem := s.mem.writeW a ((s.gpr r.reg).setWidth 8) }) ?_
    (k _ ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩)
  simp [exec, State.store8, ha, hout]

/-- `xor d, v` of an immediate. -/
theorem wp_xorI {d : Reg} {v : BitVec 32} (k : ∀ s', Upd s s' d (s.gpr d ^^^ v) → WP isa (.block is) s' Q) :
    WP isa (.block (.alu .xor d (.imm v) :: is)) s Q :=
  cons rfl (k _ (Upd.flags _ _ _ _ _ _))

/-- `and d, src` of any operand. -/
theorem wp_andS {d : Reg} {src : Src} {v : BitVec 32} (h : readSrc s src = some v)
    (k : ∀ s', Upd s s' d (s.gpr d &&& v) → WP isa (.block is) s' Q) :
    WP isa (.block (.alu .and d src :: is)) s Q :=
  cons (by simp only [exec, execAlu, h, Option.bind_some]; rfl) (k _ (Upd.flags _ _ _ _ _ _))

end

theorem readSrc_reg (s : State) (r : Reg) : readSrc s (.reg r) = some (s.gpr r) := rfl

theorem ea_at (s : State) (b : Reg) (d : Nat) : s.ea ⟨b, d⟩ = addr (s.gpr b) d := rfl

end VG.Proof.RsaPkcs1Sig.X86

end

end

/-!
# The x86 RSA padding functions: byte loops

Loops that count `ecx` down to zero, one byte per iteration (`down_loop`):
the do-while loop on `ne` runs its body `n > 0` times when each run ends
with the flags of `ecx - 1`. And the loop that writes `n` zero bytes from
`esi` (`zero_ok`), with `eax` zero (`Bignum.X86.PublicFn.clearStep`).
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Sig.X86

open VG VG.X86 VG.X86.Wp VG.WriteBytes

/-- A do-while loop on `ne` that runs its body `n > 0` times, each run
ending with the flags of `k + 1 = n`. -/
theorem down_loop {body : Prog isa} {n : Nat} (hn : 0 < n) (I : Nat → State → Prop)
    (hstep : ∀ k < n, ∀ s, I k s → WP isa body s fun s' => I (k + 1) s' ∧ s'.zf = some (decide (k + 1 = n)))
    {s : State} (h0 : I 0 s) : WP isa (.loop body .ne) s (I n) := by
  refine WP.loop (M := isa) (fun m s => ∃ k, m = n - k ∧ k < n ∧ I k s) ?_ n s ⟨0, by omega_using [], hn, h0⟩
  rintro m s ⟨k, rfl, hk, hi⟩
  refine WP.mono (hstep k hk s hi) fun s' ⟨hi', hz⟩ => ?_
  have he : isa.eval .ne s' = some (!decide (k + 1 = n)) := by
    show eval .ne s' = _; simp only [eval, hz]; rfl
  by_cases hl : k + 1 = n
  · exact .inl ⟨by rw [he]; simp [hl], hl ▸ hi'⟩
  · exact .inr ⟨by rw [he]; simp [hl], n - (k + 1), by omega_using [hk], k + 1, rfl, by omega_using [hk, hl], hi'⟩

/-- The flags of the counter, `n - k` counted down by one. -/
theorem down_z {n k : Nat} (hk : k < n) (hn : n < 2 ^ 32) :
    (BitVec.ofNat 32 (n - k) - 1 == 0) = decide (k + 1 = n) := by
  rw [ofNat_pred (by omega_using [hk]), ofNat_beq_zero (by omega_using [hn])]
  simp only [decide_eq_decide]; omega_using [hk]

theorem down_c {n k : Nat} (hk : k < n) : BitVec.ofNat 32 (n - k) - 1 = BitVec.ofNat 32 (n - (k + 1)) := by
  rw [ofNat_pred (by omega_using [hk])]; congr 1

theorem add_one32 (x : BitVec 32) (k : Nat) : x + BitVec.ofNat 32 k + 1 = x + BitVec.ofNat 32 (k + 1) := by
  rw [BitVec.add_assoc, BitVec.ofNat_add]; rfl

/-- After `k` zero bytes. -/
structure ZeroInv (s : State) (p : BitVec 32) (n k : Nat) (t : State) : Prop where
  esi : t.gpr .esi = p + BitVec.ofNat 32 k
  ecx : t.gpr .ecx = BitVec.ofNat 32 (n - k)
  eax : t.gpr .eax = 0
  other : ∀ r, r ≠ .esi → r ≠ .ecx → t.gpr r = s.gpr r
  mem : t.mem = writeBytes s.mem (p.setWidth 64) (List.replicate k 0)
  rd : t.rd = s.rd
  wr : t.wr = s.wr

theorem zero_ok {s : State} {p : BitVec 32} {n : Nat} (hn : 0 < n) (h32 : n < 2 ^ 32)
    (fit : p.toNat + n ≤ 2 ^ 32) (hp : s.gpr .esi = p) (hc : s.gpr .ecx = BitVec.ofNat 32 n)
    (hz : s.gpr .eax = 0) (hw : InRegions s.wr (p.setWidth 64) n) :
    WP isa (.loop (.block Impl.Bignum.X86.PublicFn.clearStep) .ne) s (ZeroInv s p n n) := by
  refine down_loop hn (ZeroInv s p n) (fun k hk t ht => ?_) ⟨by rw [hp]; simp, by rw [hc]; simp, hz,
    fun _ _ _ => rfl, by simp [writeBytes_nil], rfl, rfl⟩
  have hk64 : k < 2 ^ 64 := by omega_using [h32, hk]
  have ha : t.ea ⟨.esi, 0⟩ = p.setWidth 64 + BitVec.ofNat 64 k := by
    rw [ea_at, ht.esi]
    apply BitVec.eq_of_toNat_eq
    simp only [addr, BitVec.add_zero, BitVec.toNat_setWidth, BitVec.toNat_add, BitVec.toNat_ofNat]
    have := p.isLt
    rw [Nat.mod_eq_of_lt (a := k) (by omega_using [h32, hk]), Nat.mod_eq_of_lt (a := p.toNat + k) (by omega_using [fit, hk]),
      Nat.mod_eq_of_lt (a := p.toNat + k) (by omega_using [fit, hk]), Nat.mod_eq_of_lt (a := p.toNat) (by omega_using []),
      Nat.mod_eq_of_lt (a := k) (by omega_using [hk64]), Nat.mod_eq_of_lt (a := p.toNat + k) (by omega_using [fit, hk])]
  have hin : InRegions t.wr (p.setWidth 64 + BitVec.ofNat 64 k) 1 := by
    rw [ht.wr]
    obtain ⟨r, hr, hc⟩ := hw
    exact ⟨r, hr, hc.byte (by rw [Mem.sub_ofNat_toNat _ (by omega_using [hk64])]; omega_using [hk])⟩
  refine wp_store8 ha hin fun t1 u1 => wp_addi fun t2 u2 => wp_subi fun t3 u3 _ z3 => WP.block_nil ?_
  have e : ((t.gpr Reg8.al.reg).setWidth 8 : Byte) = 0 := by
    show (t.gpr .eax).setWidth 8 = 0; rw [ht.eax]; rfl
  refine ⟨⟨?_, ?_, ?_, fun r h1 h2 => ?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [u3.other _ (by decide), u2.gpr, u1.gpr, ht.esi]; exact add_one32 _ _
  · rw [u3.gpr, u2.other _ (by decide), u1.gpr, ht.ecx]; exact down_c hk
  · rw [u3.other _ (by decide), u2.other _ (by decide), u1.gpr, ht.eax]
  · rw [u3.other _ h2, u2.other _ h1, u1.gpr, ht.other _ h1 h2]
  · rw [u3.mem, u2.mem, u1.mem, e, ht.mem, List.replicate_succ', writeBytes_snoc _ _ _ _ (by simp; omega_using [hk64])]
    simp
  · rw [u3.rd, u2.rd, u1.rd, ht.rd]
  · rw [u3.wr, u2.wr, u1.wr, ht.wr]
  · rw [z3, u2.other _ (by decide), u1.gpr, ht.ecx]; exact congrArg some (down_z hk h32)

end VG.Proof.RsaPkcs1Sig.X86
