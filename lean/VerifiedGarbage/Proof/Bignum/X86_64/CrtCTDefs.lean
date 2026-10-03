import VerifiedGarbage.Proof.Bignum.X86_64.CrtChk

/-!
# RSA with the CRT on x86-64: constant time, the pieces

Two runs agree on the public data (the pointers, the lengths and `n`) but
not on the input or the private key. Each piece of `main` is constant time
for the hypotheses of its correctness lemma, with what is public fixed (a
`…Pub` structure) and the rest (`-p⁻¹`, `p`, the exponents, the values in
the arrays) existential (a `…Pre` predicate).

The small pieces are proven here; the others are stated (`…CT`) so that
the phases can be proven from them before them.
-/

namespace VG.Proof.Bignum.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64 VG.Impl.Rsa.X86_64.Crt
open VG.Proof.MlKem.X86_64

/-! ## Clearing, copying and masking an array -/

theorem GoodW.hl {L : Ws} {s : State} (h : GoodW L s) :
    ∀ i < 32, InRegions (s.rd ++ s.wr) (off L.B (8 * i)) 8 := fun i hi => by
  obtain ⟨_, hg, hZ⟩ := h
  have hn := hg.scr.nowrap
  exact hg.scr.ld (by have := hdr_lt_slot L.w 8 hi; omega)

theorem pins_of {α : Type} {Φ : α → State → Prop} {rs : List Reg} (f : α → Reg → BitVec 64)
    (h : ∀ a s, Φ a s → ∀ r ∈ rs, s.gpr r = f a r) : Pins Φ rs :=
  fun a s₁ s₂ h₁ h₂ r hr => (h a s₁ h₁ r hr).trans (h a s₂ h₂ r hr).symm

/-- `zeroArr j`, given that the taint analysis checks its header loads from
`rdi` (`by taint_decide` for a given `j`). -/
theorem zeroArr_ct {j : Nat} (hj : j < 8) {hc : VG.Taint.Hint VG.X86_64.Taint.T}
    (hT : (taint.check (Taint.ofRegs [.rdi]) (.block [.mov .r8 (.mem (hdr (sArr j))), .mov .r12 (.mem (hdr sW))])
      hc).isSome = true) :
    RelCT isa (Two GoodW) (Crt.zeroArr j) fun _ _ => True := by
  unfold Crt.zeroArr
  refine RelCT.seq (two_piece (Ψ := fun L t => t.gpr .r8 = off L.B (slot L.w j) ∧
      t.gpr .r12 = BitVec.ofNat 64 L.w) [.rdi] pins_goodW hT fun L s h => ?_)
    (two_taint [.r8, .r12] (pins_of (fun L r => if r = .r8 then off L.B (slot L.w j) else BitVec.ofNat 64 L.w)
      fun L s h r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact h.1
        · exact h.2) (by taint_decide))
  have hl := h.hl
  obtain ⟨_, hg, -⟩ := h
  exact WP.mono (WP.keep [.r8, .r12] (Q := fun t => t.gpr .r8 = off L.B (slot L.w j) ∧ t.gpr .r12 = BitVec.ofNat 64 L.w)
    (by xrun [State.ea, hdr, hg.rdi, hdrOff, hl (sArr j) (by unfold sArr; omega), hl sW (by decide),
      hg.hdr.harr j hj, hg.hdr.hw]) rfl) fun _ h => h.1

/-- `copyArr o a`, given that the taint analysis checks its header loads. -/
theorem copyArr_ct {o a : Nat} (ho : o < 8) (ha : a < 8) {hc : VG.Taint.Hint VG.X86_64.Taint.T}
    (hT : (taint.check (Taint.ofRegs [.rdi]) (.block [.mov .r12 (.mem (hdr sW)), .mov .rsi (.mem (hdr (sArr a))),
      .mov .rbx (.mem (hdr (sArr o)))]) hc).isSome = true) :
    RelCT isa (Two GoodW) (seqs (Crt.copyArr o a)) fun _ _ => True := by
  unfold Crt.copyArr
  simp only [seqs]
  refine RelCT.seq (two_piece (Ψ := fun L t => t.gpr .r12 = BitVec.ofNat 64 L.w ∧
      t.gpr .rsi = off L.B (slot L.w a) ∧ t.gpr .rbx = off L.B (slot L.w o)) [.rdi] pins_goodW hT fun L s h => ?_)
    (two_taint [.r12, .rsi, .rbx] (pins_of (fun L r => if r = .r12 then BitVec.ofNat 64 L.w else
        if r = .rsi then off L.B (slot L.w a) else off L.B (slot L.w o))
      fun L s h r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact h.1
        · exact h.2.1
        · exact h.2.2) (by taint_decide))
  have hl := h.hl
  obtain ⟨_, hg, -⟩ := h
  exact WP.mono (WP.keep [.r12, .rsi, .rbx] (Q := fun t => t.gpr .r12 = BitVec.ofNat 64 L.w ∧
      t.gpr .rsi = off L.B (slot L.w a) ∧ t.gpr .rbx = off L.B (slot L.w o))
    (by xrun [State.ea, hdr, hg.rdi, hdrOff, hl (sArr a) (by unfold sArr; omega),
      hl (sArr o) (by unfold sArr; omega), hl sW (by decide), hg.hdr.harr a ha, hg.hdr.harr o ho,
      hg.hdr.hw]) rfl) fun _ h => h.1

/-- `maskArr j`, given that the taint analysis checks its header loads. -/
theorem maskArr_ct {j : Nat} (hj : j < 8) {hc : VG.Taint.Hint VG.X86_64.Taint.T}
    (hT : (taint.check (Taint.ofRegs [.rdi]) (.block [.mov .r15 (.mem (hdr sMaskX)), .mov .r12 (.mem (hdr sW)),
      .mov .rbx (.mem (hdr (sArr j)))]) hc).isSome = true) :
    RelCT isa (Two GoodW) (seqs (Crt.maskArr j)) fun _ _ => True := by
  unfold Crt.maskArr
  simp only [seqs]
  refine RelCT.seq (two_piece (Ψ := fun L t => t.gpr .r12 = BitVec.ofNat 64 L.w ∧
      t.gpr .rbx = off L.B (slot L.w j)) [.rdi] pins_goodW hT fun L s h => ?_)
    (two_taint [.r12, .rbx] (pins_of (fun L r => if r = .r12 then BitVec.ofNat 64 L.w else off L.B (slot L.w j))
      fun L s h r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact h.1
        · exact h.2) (by taint_decide))
  have hl := h.hl
  obtain ⟨_, hg, -⟩ := h
  exact WP.mono (WP.keep [.r15, .r12, .rbx] (Q := fun t => t.gpr .r12 = BitVec.ofNat 64 L.w ∧
      t.gpr .rbx = off L.B (slot L.w j))
    (by xrun [State.ea, hdr, hg.rdi, hdrOff, hl (sArr j) (by unfold sArr; omega), hl sW (by decide),
      hl sMaskX (by decide), hg.hdr.harr j hj, hg.hdr.hw]) rfl) fun _ h => h.1

/-! ## The other pieces, as claims

Each `…Pre` is the hypotheses of the piece's correctness lemma (named in its
documentation), with the public data fixed by its `…Pub` and the secrets
existential. -/

/-- `gPow_ok`'s data, all public: it computes in `n`'s workspace with `n`
and the prime's length. -/
structure GPub where
  B : Addr
  Z : Nat
  w : Nat
  minv : BitVec 64
  N : Nat
  Bx : Addr
  wx : Nat

/-- `gPow_ok`'s hypotheses, for the workspace base in slot `sl`. -/
def GPre (sl : Nat) (p : GPub) (s : State) : Prop :=
  Good s p.B p.Z p.w p.minv ∧ slot p.w 8 ≤ p.Z ∧ 2 ≤ p.w ∧ p.w < 2 ^ 30 ∧
    wv s.mem p.B (slot p.w Public.aN) p.w = p.N ∧
    ((word s.mem p.B (slot p.w Public.aN)).toNat * p.minv.toNat + 1) % 2 ^ 64 = 0 ∧
    p.N % 2 = 1 ∧ 1 < p.N ∧
    wv s.mem p.B (slot p.w Public.aR2) p.w % p.N = 2 ^ (64 * p.w) * 2 ^ (64 * p.w) % p.N ∧
    wv s.mem p.B (slot p.w Public.aOne) p.w = 1 ∧ sl < 32 ∧ word s.mem p.B (8 * sl) = p.Bx ∧
    word s.mem p.Bx (8 * sW) = BitVec.ofNat 64 p.wx ∧ InRegions (s.rd ++ s.wr) (off p.Bx (8 * sW)) 8 ∧
    1 ≤ p.wx ∧ p.wx ≤ p.w

/-- `gPow M.mm sl` is constant time. -/
def GPowCT (M : Mont) (sl : Nat) : Prop :=
  RelCT isa (Two (GPre sl)) (seqs (Crt.gPow M.mm sl)) fun _ _ => True

/-- The public data of a prime's workspace at `off B o`: `n`'s workspace
(`B`, `Z`, `w`) and the prime's size `wx`. -/
structure XPub where
  B : Addr
  Z : Nat
  o : Nat
  w : Nat
  wx : Nat

/-- `redc_ok`'s hypotheses. -/
def RPre (j : Nat) (p : XPub) (s : State) : Prop :=
  ∃ (minv : BitVec 64) (X : Nat), SubCtx s p.B p.Z p.o p.w p.wx minv ∧ XVals s p.B p.o p.wx minv X ∧
    2 ≤ p.wx ∧ p.wx ≤ p.w ∧ p.w < 2 ^ 30 ∧ 1 < X ∧ j < 8

/-- `redc M.mm j` is constant time. -/
def RedcCT (M : Mont) (j : Nat) : Prop :=
  RelCT isa (Two (RPre j)) (seqs (Crt.redc M.mm j)) fun _ _ => True

/-- The public data of a byte string read from a prime's workspace: its
pointer and length. -/
structure SPub where
  x : XPub
  ptr : Addr
  len : Nat

/-- `crtExpLoop_ok`'s hypotheses, for the exponent's pointer and length in
`n`'s slots `sp` and `sl`. -/
def EPre (sp sl : Nat) (p : SPub) (s : State) : Prop :=
  ∃ (minv : BitVec 64) (X x y : Nat) (eb : List Byte),
    SubCtx s p.x.B p.x.Z p.x.o p.x.w p.x.wx minv ∧ 2 ≤ p.x.wx ∧ p.x.wx ≤ p.x.w ∧ p.x.w < 2 ^ 30 ∧
    wv s.mem (off p.x.B p.x.o) (slot p.x.wx Public.aN) p.x.wx = X ∧
    ((word s.mem (off p.x.B p.x.o) (slot p.x.wx Public.aN)).toNat * minv.toNat + 1) % 2 ^ 64 = 0 ∧
    X % 2 = 1 ∧ wv s.mem (off p.x.B p.x.o) (slot p.x.wx aXc) p.x.wx < X ∧
    wv s.mem (off p.x.B p.x.o) (slot p.x.wx aXc) p.x.wx % X = x * 2 ^ (64 * p.x.wx) % X ∧
    wv s.mem (off p.x.B p.x.o) (slot p.x.wx Public.aY) p.x.wx < X ∧
    wv s.mem (off p.x.B p.x.o) (slot p.x.wx Public.aY) p.x.wx % X = y * 2 ^ (64 * p.x.wx) % X ∧
    sp < 32 ∧ sl < 32 ∧ word s.mem p.x.B (8 * sp) = p.ptr ∧
    word s.mem p.x.B (8 * sl) = BitVec.ofNat 64 eb.length ∧ eb.length = p.len ∧ 1 ≤ eb.length ∧
    eb.length ≤ 1024 ∧ Src s p.x.B p.x.Z p.ptr eb

/-- `expLoop M.mm sp sl` is constant time. -/
def ExpCT (M : Mont) (sp sl : Nat) : Prop :=
  RelCT isa (Two (EPre sp sl)) (seqs (Crt.expLoop M.mm sp sl)) fun _ _ => True

/-- `primeLoad_ok`'s hypotheses. -/
def LPre (j sp sl : Nat) (p : SPub) (s : State) : Prop :=
  ∃ (minv : BitVec 64) (bs : List Byte), SubCtx s p.x.B p.x.Z p.x.o p.x.w p.x.wx minv ∧ 2 ≤ p.x.wx ∧
    p.x.wx ≤ p.x.w ∧ p.x.w < 2 ^ 30 ∧ j < 8 ∧ sp < 32 ∧ sl < 32 ∧ word s.mem p.x.B (8 * sp) = p.ptr ∧
    word s.mem p.x.B (8 * sl) = BitVec.ofNat 64 bs.length ∧ bs.length = p.len ∧ Src s p.x.B p.x.Z p.ptr bs ∧
    1 ≤ bs.length ∧ bs.length < 2 ^ 31 ∧ (bs.length + 7) / 8 ≤ p.x.wx

/-- `loadArr j sp sl` is constant time. -/
def LoadCT (j sp sl : Nat) : Prop :=
  RelCT isa (Two (LPre j sp sl)) (seqs (loadArr j sp sl)) fun _ _ => True

/-- The public data of the setup: `n`'s workspace, `-n⁻¹`, the primes'
lengths and the pointers to `p`, `q` and `qInv`. -/
structure SetupPub where
  B : Addr
  Z : Nat
  w : Nat
  minv : BitVec 64
  pl : Nat
  ql : Nat
  pp : Addr
  qp : Addr
  ip : Addr

/-- `primesSetup_ok`'s hypotheses. -/
def SetupPre (p : SetupPub) (s : State) : Prop :=
  ∃ pb qb ib : List Byte, Good s p.B p.Z p.w p.minv ∧ 8 ≤ p.w ∧ p.w < 2 ^ 28 ∧
    offQ p.w p.pl + slot (wsWords p.ql) 8 ≤ p.Z ∧
    word s.mem p.B (8 * sPlen) = BitVec.ofNat 64 p.pl ∧ word s.mem p.B (8 * sQlen) = BitVec.ofNat 64 p.ql ∧
    word s.mem p.B (8 * sP) = p.pp ∧ word s.mem p.B (8 * sQ) = p.qp ∧ word s.mem p.B (8 * sQinv) = p.ip ∧
    Src s p.B p.Z p.pp pb ∧ Src s p.B p.Z p.qp qb ∧ Src s p.B p.Z p.ip ib ∧ pb.length = p.pl ∧
    qb.length = p.ql ∧ ib.length = p.pl ∧ 1 ≤ p.pl ∧ p.pl < 8 * p.w ∧ 1 ≤ p.ql ∧ p.ql < 8 * p.w

/-- `primesSetup` is constant time. -/
def SetupCT : Prop := RelCT isa (Two SetupPre) (seqs primesSetup) fun _ _ => True

/-- The public data of the checks: `n`'s workspace, `-n⁻¹`, `n` and the
primes' workspaces. -/
structure ChecksPub where
  B : Addr
  Z : Nat
  w : Nat
  minv : BitVec 64
  N : Nat
  op : Nat
  oq : Nat
  wp : Nat
  wq : Nat

/-- `checks_ok`'s hypotheses. -/
def ChecksPre (p : ChecksPub) (s : State) : Prop :=
  ∃ (mp mq : BitVec 64) (P Q QI : Nat) (m0 : Bool), Good s p.B p.Z p.w p.minv ∧ 8 ≤ p.w ∧ p.w < 2 ^ 28 ∧
    slot p.w 8 ≤ p.op ∧ p.op + slot p.wp 8 ≤ p.oq ∧ p.oq + slot p.wq 8 ≤ p.Z ∧ 2 ≤ p.wp ∧ p.wp ≤ p.w ∧
    2 ≤ p.wq ∧ p.wq ≤ p.w ∧ word s.mem p.B (8 * sWsP) = off p.B p.op ∧
    word s.mem p.B (8 * sWsQ) = off p.B p.oq ∧ WsAt s.mem p.B p.op p.wp mp ∧ WsAt s.mem p.B p.oq p.wq mq ∧
    wv s.mem p.B (slot p.w Public.aN) p.w = p.N ∧ word s.mem p.B (8 * Public.sMask) = mask m0 ∧
    wv s.mem (off p.B p.op) (slot p.wp Public.aN) p.wp = P ∧
    wv s.mem (off p.B p.oq) (slot p.wq Public.aN) p.wq = Q ∧
    wv s.mem (off p.B p.op) (slot p.wp aChunk) p.wp = QI ∧ p.N % 2 = 1

/-- `checks` is constant time. -/
def ChecksCT : Prop := RelCT isa (Two ChecksPre) (seqs checks) fun _ _ => True

/-- The public data of the phases' parts: `n`'s workspace, `-n⁻¹`, `n`, the
prime's workspace (its base in slot `sl`). -/
structure UPub where
  B : Addr
  Z : Nat
  w : Nat
  minv : BitVec 64
  N : Nat
  o : Nat
  wx : Nat

/-- `unitPhase_ok`'s hypotheses. -/
def UPre (sl : Nat) (p : UPub) (s : State) : Prop :=
  ∃ (mx : BitVec 64) (X : Nat), Good s p.B p.Z p.w p.minv ∧ 8 ≤ p.w ∧ p.w < 2 ^ 28 ∧ slot p.w 8 ≤ p.o ∧
    p.o + slot p.wx 8 ≤ p.Z ∧ 2 ≤ p.wx ∧ p.wx ≤ p.w ∧ sl < 32 ∧ sl ≠ Crt.sD ∧ sl ≠ Public.sCnt ∧
    word s.mem p.B (8 * sl) = off p.B p.o ∧ WsAt s.mem p.B p.o p.wx mx ∧ NVals s p.B p.w p.minv p.N ∧
    p.N % 2 = 1 ∧ 1 < p.N ∧ XVals s p.B p.o p.wx mx X ∧ 1 < X ∧ X % 2 = 1

/-- The phases' first part (`unitPhase_ok`) is constant time. -/
def UnitCT (M : Mont) (sl : Nat) : Prop :=
  RelCT isa (Two (UPre sl)) (seqs (Crt.gPow M.mm sl ++ [.block [.mov .rdi (.mem (hdr sl))]] ++
    redc M.mm Public.aY ++ copyArr Public.aY aXc ++ [.block [leave]])) fun _ _ => True

/-- `powPhase_ok`'s hypotheses, for the exponent's pointer and length in
slots `sd` and `slen`. -/
def PwPre (sl sd slen : Nat) (p : SPub) (s : State) : Prop :=
  ∃ (minv mx : BitVec 64) (N X C : Nat) (eb : List Byte), Good s p.x.B p.x.Z p.x.w minv ∧ p.x.w < 2 ^ 28 ∧
    slot p.x.w 8 ≤ p.x.o ∧ p.x.o + slot p.x.wx 8 ≤ p.x.Z ∧ 2 ≤ p.x.wx ∧ p.x.wx ≤ p.x.w ∧ sl < 32 ∧
    word s.mem p.x.B (8 * sl) = off p.x.B p.x.o ∧ WsAt s.mem p.x.B p.x.o p.x.wx mx ∧
    XVals s p.x.B p.x.o p.x.wx mx X ∧ 1 < X ∧ X % 2 = 1 ∧
    wv s.mem p.x.B (slot p.x.w Public.aY) p.x.w % N = C * 2 ^ (64 * p.x.wx * (nChunks p.x.w p.x.wx + 1)) % N ∧
    wv s.mem (off p.x.B p.x.o) (slot p.x.wx Public.aY) p.x.wx < X ∧
    (X ∣ N → wv s.mem (off p.x.B p.x.o) (slot p.x.wx Public.aY) p.x.wx % X = 2 ^ (64 * p.x.wx) % X) ∧
    sd < 32 ∧ slen < 32 ∧ word s.mem p.x.B (8 * sd) = p.ptr ∧
    word s.mem p.x.B (8 * slen) = BitVec.ofNat 64 eb.length ∧ eb.length = p.len ∧ 1 ≤ eb.length ∧
    eb.length ≤ 1024 ∧ Src s p.x.B p.x.Z p.ptr eb

/-- The phases' exponentiation (`powPhase_ok`) is constant time. -/
def PowCT (M : Mont) (sl sd slen : Nat) : Prop :=
  RelCT isa (Two (PwPre sl sd slen)) (seqs ([.block [.mov .rdi (.mem (hdr sl))]] ++ redc M.mm Public.aY ++
    Crt.expLoop M.mm sd slen)) fun _ _ => True

/-- The public data of a prime's phase: `n`'s workspace, `-n⁻¹`, `n`, the
prime's workspace and the exponent's pointer and length. -/
structure PhasePub where
  B : Addr
  Z : Nat
  w : Nat
  minv : BitVec 64
  N : Nat
  o : Nat
  wx : Nat
  ep : Addr
  len : Nat

/-- `qPhase_ok`'s hypotheses. -/
def QPre (p : PhasePub) (s : State) : Prop :=
  ∃ (mx : BitVec 64) (X C : Nat) (eb : List Byte), Good s p.B p.Z p.w p.minv ∧ 8 ≤ p.w ∧ p.w < 2 ^ 28 ∧
    slot p.w 8 ≤ p.o ∧ p.o + slot p.wx 8 ≤ p.Z ∧ 2 ≤ p.wx ∧ p.wx ≤ p.w ∧
    word s.mem p.B (8 * sWsQ) = off p.B p.o ∧ WsAt s.mem p.B p.o p.wx mx ∧ NVals s p.B p.w p.minv p.N ∧
    p.N % 2 = 1 ∧ 1 < p.N ∧ wv s.mem p.B (slot p.w Public.aXm) p.w % p.N = C * 2 ^ (64 * p.w) % p.N ∧
    XVals s p.B p.o p.wx mx X ∧ 1 < X ∧ X % 2 = 1 ∧ word s.mem p.B (8 * sDq) = p.ep ∧
    word s.mem p.B (8 * sQlen) = BitVec.ofNat 64 eb.length ∧ eb.length = p.len ∧ 1 ≤ eb.length ∧
    eb.length ≤ 1024 ∧ Src s p.B p.Z p.ep eb

/-- `qPhase M.mm` is constant time. -/
def QPhaseCT (M : Mont) : Prop := RelCT isa (Two QPre) (seqs (qPhase M.mm)) fun _ _ => True

/-- The public data of `p`'s phase: also `q`'s workspace and `qInv`'s
pointer. -/
structure PPhasePub where
  ph : PhasePub
  oq : Nat
  wq : Nat
  qp : Addr

/-- `pPhase_ok`'s hypotheses. -/
def PPre (p : PPhasePub) (s : State) : Prop :=
  ∃ (mx mq : BitVec 64) (X C : Nat) (eb qib : List Byte) (c : Bool), Good s p.ph.B p.ph.Z p.ph.w p.ph.minv ∧
    8 ≤ p.ph.w ∧ p.ph.w < 2 ^ 28 ∧ slot p.ph.w 8 ≤ p.ph.o ∧ p.ph.o + slot p.ph.wx 8 ≤ p.oq ∧
    p.oq + slot p.wq 8 ≤ p.ph.Z ∧ 2 ≤ p.ph.wx ∧ p.ph.wx ≤ p.ph.w ∧ 1 ≤ p.wq ∧ p.wq ≤ p.ph.w ∧
    word s.mem p.ph.B (8 * sWsP) = off p.ph.B p.ph.o ∧ WsAt s.mem p.ph.B p.ph.o p.ph.wx mx ∧
    word s.mem p.ph.B (8 * sWsQ) = off p.ph.B p.oq ∧ WsAt s.mem p.ph.B p.oq p.wq mq ∧
    NVals s p.ph.B p.ph.w p.ph.minv p.ph.N ∧ p.ph.N % 2 = 1 ∧ 1 < p.ph.N ∧
    wv s.mem p.ph.B (slot p.ph.w Public.aXm) p.ph.w % p.ph.N = C * 2 ^ (64 * p.ph.w) % p.ph.N ∧
    XVals s p.ph.B p.ph.o p.ph.wx mx X ∧ 1 < X ∧ X % 2 = 1 ∧
    word s.mem (off p.ph.B p.ph.o) (8 * sMaskX) = mask c ∧ (c = true → X ∣ p.ph.N) ∧
    word s.mem p.ph.B (8 * sDp) = p.ph.ep ∧ word s.mem p.ph.B (8 * sPlen) = BitVec.ofNat 64 eb.length ∧
    eb.length = p.ph.len ∧ 1 ≤ eb.length ∧ eb.length ≤ 1024 ∧ Src s p.ph.B p.ph.Z p.ph.ep eb ∧
    word s.mem p.ph.B (8 * sQinv) = p.qp ∧ qib.length = eb.length ∧ Src s p.ph.B p.ph.Z p.qp qib ∧
    (qib.length + 7) / 8 ≤ p.ph.wx ∧ (c = true → Spec.Rsa.os2ip qib < X)

/-- `pPhase M.mm` is constant time. -/
def PPhaseCT (M : Mont) : Prop := RelCT isa (Two PPre) (seqs (pPhase M.mm)) fun _ _ => True

end VG.Proof.Bignum.X86_64
