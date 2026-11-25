# Does Apple lose ML-KEM time to the (2,8) mix? (written before the code)

Counts per vector round: (0,0) is 66 operations but for iota; es=2, bs=8 adds
2*2 + 8 = 12, so 78 (+18%). A core whose vector units all run FEAT_SHA3 gains
nothing from the mix and pays up to 18% of the vector work where that is the
bound. ML-KEM spends perhaps half of its time in Keccak, so at most ~9%.

Existing microbenchmarks do not decide it (one run each, +-20%): (0,0) 153-245 ns,
(2,8) 206-246 ns, old x2 166-238 ns.

Experiment: the two- and three-state functions of #6496 with (0,0) in the order
written, nothing else changed, against #6496's head, on Apple, one run, default
features: modules mlkem768 mlkem1024, and sha3 as a control: its single-state
code is (0,0) already and is identical in both builds, so what differs there
is noise. sha3-256/1024 therefore cannot be won back by a mix; its 7-9% has
another cause or is noise. #6496 against the old base is run 45667860585.

It separates from the noise if every ML-KEM operation moves the same way by
more than the largest change among the sha3 controls.
