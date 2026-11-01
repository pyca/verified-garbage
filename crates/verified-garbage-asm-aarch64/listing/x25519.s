// The functions of `src/x25519.rs` of `verified-garbage-asm-aarch64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_x25519:
	str x19, [x3, #0]
	str x20, [x3, #8]
	str x21, [x3, #16]
	str x22, [x3, #24]
	str x23, [x3, #32]
	str x24, [x3, #40]
	movz x20, #1, lsl #0
	ldrb w17, [x1, #0]
	lsr x19, x17, #0
	and x19, x19, x20
	strb w19, [x3, #1984]
	lsr x19, x17, #1
	and x19, x19, x20
	strb w19, [x3, #1985]
	lsr x19, x17, #2
	and x19, x19, x20
	strb w19, [x3, #1986]
	lsr x19, x17, #3
	and x19, x19, x20
	strb w19, [x3, #1987]
	lsr x19, x17, #4
	and x19, x19, x20
	strb w19, [x3, #1988]
	lsr x19, x17, #5
	and x19, x19, x20
	strb w19, [x3, #1989]
	lsr x19, x17, #6
	and x19, x19, x20
	strb w19, [x3, #1990]
	lsr x19, x17, #7
	and x19, x19, x20
	strb w19, [x3, #1991]
	ldrb w17, [x1, #1]
	lsr x19, x17, #0
	and x19, x19, x20
	strb w19, [x3, #1992]
	lsr x19, x17, #1
	and x19, x19, x20
	strb w19, [x3, #1993]
	lsr x19, x17, #2
	and x19, x19, x20
	strb w19, [x3, #1994]
	lsr x19, x17, #3
	and x19, x19, x20
	strb w19, [x3, #1995]
	lsr x19, x17, #4
	and x19, x19, x20
	strb w19, [x3, #1996]
	lsr x19, x17, #5
	and x19, x19, x20
	strb w19, [x3, #1997]
	lsr x19, x17, #6
	and x19, x19, x20
	strb w19, [x3, #1998]
	lsr x19, x17, #7
	and x19, x19, x20
	strb w19, [x3, #1999]
	ldrb w17, [x1, #2]
	lsr x19, x17, #0
	and x19, x19, x20
	strb w19, [x3, #2000]
	lsr x19, x17, #1
	and x19, x19, x20
	strb w19, [x3, #2001]
	lsr x19, x17, #2
	and x19, x19, x20
	strb w19, [x3, #2002]
	lsr x19, x17, #3
	and x19, x19, x20
	strb w19, [x3, #2003]
	lsr x19, x17, #4
	and x19, x19, x20
	strb w19, [x3, #2004]
	lsr x19, x17, #5
	and x19, x19, x20
	strb w19, [x3, #2005]
	lsr x19, x17, #6
	and x19, x19, x20
	strb w19, [x3, #2006]
	lsr x19, x17, #7
	and x19, x19, x20
	strb w19, [x3, #2007]
	ldrb w17, [x1, #3]
	lsr x19, x17, #0
	and x19, x19, x20
	strb w19, [x3, #2008]
	lsr x19, x17, #1
	and x19, x19, x20
	strb w19, [x3, #2009]
	lsr x19, x17, #2
	and x19, x19, x20
	strb w19, [x3, #2010]
	lsr x19, x17, #3
	and x19, x19, x20
	strb w19, [x3, #2011]
	lsr x19, x17, #4
	and x19, x19, x20
	strb w19, [x3, #2012]
	lsr x19, x17, #5
	and x19, x19, x20
	strb w19, [x3, #2013]
	lsr x19, x17, #6
	and x19, x19, x20
	strb w19, [x3, #2014]
	lsr x19, x17, #7
	and x19, x19, x20
	strb w19, [x3, #2015]
	ldrb w17, [x1, #4]
	lsr x19, x17, #0
	and x19, x19, x20
	strb w19, [x3, #2016]
	lsr x19, x17, #1
	and x19, x19, x20
	strb w19, [x3, #2017]
	lsr x19, x17, #2
	and x19, x19, x20
	strb w19, [x3, #2018]
	lsr x19, x17, #3
	and x19, x19, x20
	strb w19, [x3, #2019]
	lsr x19, x17, #4
	and x19, x19, x20
	strb w19, [x3, #2020]
	lsr x19, x17, #5
	and x19, x19, x20
	strb w19, [x3, #2021]
	lsr x19, x17, #6
	and x19, x19, x20
	strb w19, [x3, #2022]
	lsr x19, x17, #7
	and x19, x19, x20
	strb w19, [x3, #2023]
	ldrb w17, [x1, #5]
	lsr x19, x17, #0
	and x19, x19, x20
	strb w19, [x3, #2024]
	lsr x19, x17, #1
	and x19, x19, x20
	strb w19, [x3, #2025]
	lsr x19, x17, #2
	and x19, x19, x20
	strb w19, [x3, #2026]
	lsr x19, x17, #3
	and x19, x19, x20
	strb w19, [x3, #2027]
	lsr x19, x17, #4
	and x19, x19, x20
	strb w19, [x3, #2028]
	lsr x19, x17, #5
	and x19, x19, x20
	strb w19, [x3, #2029]
	lsr x19, x17, #6
	and x19, x19, x20
	strb w19, [x3, #2030]
	lsr x19, x17, #7
	and x19, x19, x20
	strb w19, [x3, #2031]
	ldrb w17, [x1, #6]
	lsr x19, x17, #0
	and x19, x19, x20
	strb w19, [x3, #2032]
	lsr x19, x17, #1
	and x19, x19, x20
	strb w19, [x3, #2033]
	lsr x19, x17, #2
	and x19, x19, x20
	strb w19, [x3, #2034]
	lsr x19, x17, #3
	and x19, x19, x20
	strb w19, [x3, #2035]
	lsr x19, x17, #4
	and x19, x19, x20
	strb w19, [x3, #2036]
	lsr x19, x17, #5
	and x19, x19, x20
	strb w19, [x3, #2037]
	lsr x19, x17, #6
	and x19, x19, x20
	strb w19, [x3, #2038]
	lsr x19, x17, #7
	and x19, x19, x20
	strb w19, [x3, #2039]
	ldrb w17, [x1, #7]
	lsr x19, x17, #0
	and x19, x19, x20
	strb w19, [x3, #2040]
	lsr x19, x17, #1
	and x19, x19, x20
	strb w19, [x3, #2041]
	lsr x19, x17, #2
	and x19, x19, x20
	strb w19, [x3, #2042]
	lsr x19, x17, #3
	and x19, x19, x20
	strb w19, [x3, #2043]
	lsr x19, x17, #4
	and x19, x19, x20
	strb w19, [x3, #2044]
	lsr x19, x17, #5
	and x19, x19, x20
	strb w19, [x3, #2045]
	lsr x19, x17, #6
	and x19, x19, x20
	strb w19, [x3, #2046]
	lsr x19, x17, #7
	and x19, x19, x20
	strb w19, [x3, #2047]
	ldrb w17, [x1, #8]
	lsr x19, x17, #0
	and x19, x19, x20
	strb w19, [x3, #2048]
	lsr x19, x17, #1
	and x19, x19, x20
	strb w19, [x3, #2049]
	lsr x19, x17, #2
	and x19, x19, x20
	strb w19, [x3, #2050]
	lsr x19, x17, #3
	and x19, x19, x20
	strb w19, [x3, #2051]
	lsr x19, x17, #4
	and x19, x19, x20
	strb w19, [x3, #2052]
	lsr x19, x17, #5
	and x19, x19, x20
	strb w19, [x3, #2053]
	lsr x19, x17, #6
	and x19, x19, x20
	strb w19, [x3, #2054]
	lsr x19, x17, #7
	and x19, x19, x20
	strb w19, [x3, #2055]
	ldrb w17, [x1, #9]
	lsr x19, x17, #0
	and x19, x19, x20
	strb w19, [x3, #2056]
	lsr x19, x17, #1
	and x19, x19, x20
	strb w19, [x3, #2057]
	lsr x19, x17, #2
	and x19, x19, x20
	strb w19, [x3, #2058]
	lsr x19, x17, #3
	and x19, x19, x20
	strb w19, [x3, #2059]
	lsr x19, x17, #4
	and x19, x19, x20
	strb w19, [x3, #2060]
	lsr x19, x17, #5
	and x19, x19, x20
	strb w19, [x3, #2061]
	lsr x19, x17, #6
	and x19, x19, x20
	strb w19, [x3, #2062]
	lsr x19, x17, #7
	and x19, x19, x20
	strb w19, [x3, #2063]
	ldrb w17, [x1, #10]
	lsr x19, x17, #0
	and x19, x19, x20
	strb w19, [x3, #2064]
	lsr x19, x17, #1
	and x19, x19, x20
	strb w19, [x3, #2065]
	lsr x19, x17, #2
	and x19, x19, x20
	strb w19, [x3, #2066]
	lsr x19, x17, #3
	and x19, x19, x20
	strb w19, [x3, #2067]
	lsr x19, x17, #4
	and x19, x19, x20
	strb w19, [x3, #2068]
	lsr x19, x17, #5
	and x19, x19, x20
	strb w19, [x3, #2069]
	lsr x19, x17, #6
	and x19, x19, x20
	strb w19, [x3, #2070]
	lsr x19, x17, #7
	and x19, x19, x20
	strb w19, [x3, #2071]
	ldrb w17, [x1, #11]
	lsr x19, x17, #0
	and x19, x19, x20
	strb w19, [x3, #2072]
	lsr x19, x17, #1
	and x19, x19, x20
	strb w19, [x3, #2073]
	lsr x19, x17, #2
	and x19, x19, x20
	strb w19, [x3, #2074]
	lsr x19, x17, #3
	and x19, x19, x20
	strb w19, [x3, #2075]
	lsr x19, x17, #4
	and x19, x19, x20
	strb w19, [x3, #2076]
	lsr x19, x17, #5
	and x19, x19, x20
	strb w19, [x3, #2077]
	lsr x19, x17, #6
	and x19, x19, x20
	strb w19, [x3, #2078]
	lsr x19, x17, #7
	and x19, x19, x20
	strb w19, [x3, #2079]
	ldrb w17, [x1, #12]
	lsr x19, x17, #0
	and x19, x19, x20
	strb w19, [x3, #2080]
	lsr x19, x17, #1
	and x19, x19, x20
	strb w19, [x3, #2081]
	lsr x19, x17, #2
	and x19, x19, x20
	strb w19, [x3, #2082]
	lsr x19, x17, #3
	and x19, x19, x20
	strb w19, [x3, #2083]
	lsr x19, x17, #4
	and x19, x19, x20
	strb w19, [x3, #2084]
	lsr x19, x17, #5
	and x19, x19, x20
	strb w19, [x3, #2085]
	lsr x19, x17, #6
	and x19, x19, x20
	strb w19, [x3, #2086]
	lsr x19, x17, #7
	and x19, x19, x20
	strb w19, [x3, #2087]
	ldrb w17, [x1, #13]
	lsr x19, x17, #0
	and x19, x19, x20
	strb w19, [x3, #2088]
	lsr x19, x17, #1
	and x19, x19, x20
	strb w19, [x3, #2089]
	lsr x19, x17, #2
	and x19, x19, x20
	strb w19, [x3, #2090]
	lsr x19, x17, #3
	and x19, x19, x20
	strb w19, [x3, #2091]
	lsr x19, x17, #4
	and x19, x19, x20
	strb w19, [x3, #2092]
	lsr x19, x17, #5
	and x19, x19, x20
	strb w19, [x3, #2093]
	lsr x19, x17, #6
	and x19, x19, x20
	strb w19, [x3, #2094]
	lsr x19, x17, #7
	and x19, x19, x20
	strb w19, [x3, #2095]
	ldrb w17, [x1, #14]
	lsr x19, x17, #0
	and x19, x19, x20
	strb w19, [x3, #2096]
	lsr x19, x17, #1
	and x19, x19, x20
	strb w19, [x3, #2097]
	lsr x19, x17, #2
	and x19, x19, x20
	strb w19, [x3, #2098]
	lsr x19, x17, #3
	and x19, x19, x20
	strb w19, [x3, #2099]
	lsr x19, x17, #4
	and x19, x19, x20
	strb w19, [x3, #2100]
	lsr x19, x17, #5
	and x19, x19, x20
	strb w19, [x3, #2101]
	lsr x19, x17, #6
	and x19, x19, x20
	strb w19, [x3, #2102]
	lsr x19, x17, #7
	and x19, x19, x20
	strb w19, [x3, #2103]
	ldrb w17, [x1, #15]
	lsr x19, x17, #0
	and x19, x19, x20
	strb w19, [x3, #2104]
	lsr x19, x17, #1
	and x19, x19, x20
	strb w19, [x3, #2105]
	lsr x19, x17, #2
	and x19, x19, x20
	strb w19, [x3, #2106]
	lsr x19, x17, #3
	and x19, x19, x20
	strb w19, [x3, #2107]
	lsr x19, x17, #4
	and x19, x19, x20
	strb w19, [x3, #2108]
	lsr x19, x17, #5
	and x19, x19, x20
	strb w19, [x3, #2109]
	lsr x19, x17, #6
	and x19, x19, x20
	strb w19, [x3, #2110]
	lsr x19, x17, #7
	and x19, x19, x20
	strb w19, [x3, #2111]
	ldrb w17, [x1, #16]
	lsr x19, x17, #0
	and x19, x19, x20
	strb w19, [x3, #2112]
	lsr x19, x17, #1
	and x19, x19, x20
	strb w19, [x3, #2113]
	lsr x19, x17, #2
	and x19, x19, x20
	strb w19, [x3, #2114]
	lsr x19, x17, #3
	and x19, x19, x20
	strb w19, [x3, #2115]
	lsr x19, x17, #4
	and x19, x19, x20
	strb w19, [x3, #2116]
	lsr x19, x17, #5
	and x19, x19, x20
	strb w19, [x3, #2117]
	lsr x19, x17, #6
	and x19, x19, x20
	strb w19, [x3, #2118]
	lsr x19, x17, #7
	and x19, x19, x20
	strb w19, [x3, #2119]
	ldrb w17, [x1, #17]
	lsr x19, x17, #0
	and x19, x19, x20
	strb w19, [x3, #2120]
	lsr x19, x17, #1
	and x19, x19, x20
	strb w19, [x3, #2121]
	lsr x19, x17, #2
	and x19, x19, x20
	strb w19, [x3, #2122]
	lsr x19, x17, #3
	and x19, x19, x20
	strb w19, [x3, #2123]
	lsr x19, x17, #4
	and x19, x19, x20
	strb w19, [x3, #2124]
	lsr x19, x17, #5
	and x19, x19, x20
	strb w19, [x3, #2125]
	lsr x19, x17, #6
	and x19, x19, x20
	strb w19, [x3, #2126]
	lsr x19, x17, #7
	and x19, x19, x20
	strb w19, [x3, #2127]
	ldrb w17, [x1, #18]
	lsr x19, x17, #0
	and x19, x19, x20
	strb w19, [x3, #2128]
	lsr x19, x17, #1
	and x19, x19, x20
	strb w19, [x3, #2129]
	lsr x19, x17, #2
	and x19, x19, x20
	strb w19, [x3, #2130]
	lsr x19, x17, #3
	and x19, x19, x20
	strb w19, [x3, #2131]
	lsr x19, x17, #4
	and x19, x19, x20
	strb w19, [x3, #2132]
	lsr x19, x17, #5
	and x19, x19, x20
	strb w19, [x3, #2133]
	lsr x19, x17, #6
	and x19, x19, x20
	strb w19, [x3, #2134]
	lsr x19, x17, #7
	and x19, x19, x20
	strb w19, [x3, #2135]
	ldrb w17, [x1, #19]
	lsr x19, x17, #0
	and x19, x19, x20
	strb w19, [x3, #2136]
	lsr x19, x17, #1
	and x19, x19, x20
	strb w19, [x3, #2137]
	lsr x19, x17, #2
	and x19, x19, x20
	strb w19, [x3, #2138]
	lsr x19, x17, #3
	and x19, x19, x20
	strb w19, [x3, #2139]
	lsr x19, x17, #4
	and x19, x19, x20
	strb w19, [x3, #2140]
	lsr x19, x17, #5
	and x19, x19, x20
	strb w19, [x3, #2141]
	lsr x19, x17, #6
	and x19, x19, x20
	strb w19, [x3, #2142]
	lsr x19, x17, #7
	and x19, x19, x20
	strb w19, [x3, #2143]
	ldrb w17, [x1, #20]
	lsr x19, x17, #0
	and x19, x19, x20
	strb w19, [x3, #2144]
	lsr x19, x17, #1
	and x19, x19, x20
	strb w19, [x3, #2145]
	lsr x19, x17, #2
	and x19, x19, x20
	strb w19, [x3, #2146]
	lsr x19, x17, #3
	and x19, x19, x20
	strb w19, [x3, #2147]
	lsr x19, x17, #4
	and x19, x19, x20
	strb w19, [x3, #2148]
	lsr x19, x17, #5
	and x19, x19, x20
	strb w19, [x3, #2149]
	lsr x19, x17, #6
	and x19, x19, x20
	strb w19, [x3, #2150]
	lsr x19, x17, #7
	and x19, x19, x20
	strb w19, [x3, #2151]
	ldrb w17, [x1, #21]
	lsr x19, x17, #0
	and x19, x19, x20
	strb w19, [x3, #2152]
	lsr x19, x17, #1
	and x19, x19, x20
	strb w19, [x3, #2153]
	lsr x19, x17, #2
	and x19, x19, x20
	strb w19, [x3, #2154]
	lsr x19, x17, #3
	and x19, x19, x20
	strb w19, [x3, #2155]
	lsr x19, x17, #4
	and x19, x19, x20
	strb w19, [x3, #2156]
	lsr x19, x17, #5
	and x19, x19, x20
	strb w19, [x3, #2157]
	lsr x19, x17, #6
	and x19, x19, x20
	strb w19, [x3, #2158]
	lsr x19, x17, #7
	and x19, x19, x20
	strb w19, [x3, #2159]
	ldrb w17, [x1, #22]
	lsr x19, x17, #0
	and x19, x19, x20
	strb w19, [x3, #2160]
	lsr x19, x17, #1
	and x19, x19, x20
	strb w19, [x3, #2161]
	lsr x19, x17, #2
	and x19, x19, x20
	strb w19, [x3, #2162]
	lsr x19, x17, #3
	and x19, x19, x20
	strb w19, [x3, #2163]
	lsr x19, x17, #4
	and x19, x19, x20
	strb w19, [x3, #2164]
	lsr x19, x17, #5
	and x19, x19, x20
	strb w19, [x3, #2165]
	lsr x19, x17, #6
	and x19, x19, x20
	strb w19, [x3, #2166]
	lsr x19, x17, #7
	and x19, x19, x20
	strb w19, [x3, #2167]
	ldrb w17, [x1, #23]
	lsr x19, x17, #0
	and x19, x19, x20
	strb w19, [x3, #2168]
	lsr x19, x17, #1
	and x19, x19, x20
	strb w19, [x3, #2169]
	lsr x19, x17, #2
	and x19, x19, x20
	strb w19, [x3, #2170]
	lsr x19, x17, #3
	and x19, x19, x20
	strb w19, [x3, #2171]
	lsr x19, x17, #4
	and x19, x19, x20
	strb w19, [x3, #2172]
	lsr x19, x17, #5
	and x19, x19, x20
	strb w19, [x3, #2173]
	lsr x19, x17, #6
	and x19, x19, x20
	strb w19, [x3, #2174]
	lsr x19, x17, #7
	and x19, x19, x20
	strb w19, [x3, #2175]
	ldrb w17, [x1, #24]
	lsr x19, x17, #0
	and x19, x19, x20
	strb w19, [x3, #2176]
	lsr x19, x17, #1
	and x19, x19, x20
	strb w19, [x3, #2177]
	lsr x19, x17, #2
	and x19, x19, x20
	strb w19, [x3, #2178]
	lsr x19, x17, #3
	and x19, x19, x20
	strb w19, [x3, #2179]
	lsr x19, x17, #4
	and x19, x19, x20
	strb w19, [x3, #2180]
	lsr x19, x17, #5
	and x19, x19, x20
	strb w19, [x3, #2181]
	lsr x19, x17, #6
	and x19, x19, x20
	strb w19, [x3, #2182]
	lsr x19, x17, #7
	and x19, x19, x20
	strb w19, [x3, #2183]
	ldrb w17, [x1, #25]
	lsr x19, x17, #0
	and x19, x19, x20
	strb w19, [x3, #2184]
	lsr x19, x17, #1
	and x19, x19, x20
	strb w19, [x3, #2185]
	lsr x19, x17, #2
	and x19, x19, x20
	strb w19, [x3, #2186]
	lsr x19, x17, #3
	and x19, x19, x20
	strb w19, [x3, #2187]
	lsr x19, x17, #4
	and x19, x19, x20
	strb w19, [x3, #2188]
	lsr x19, x17, #5
	and x19, x19, x20
	strb w19, [x3, #2189]
	lsr x19, x17, #6
	and x19, x19, x20
	strb w19, [x3, #2190]
	lsr x19, x17, #7
	and x19, x19, x20
	strb w19, [x3, #2191]
	ldrb w17, [x1, #26]
	lsr x19, x17, #0
	and x19, x19, x20
	strb w19, [x3, #2192]
	lsr x19, x17, #1
	and x19, x19, x20
	strb w19, [x3, #2193]
	lsr x19, x17, #2
	and x19, x19, x20
	strb w19, [x3, #2194]
	lsr x19, x17, #3
	and x19, x19, x20
	strb w19, [x3, #2195]
	lsr x19, x17, #4
	and x19, x19, x20
	strb w19, [x3, #2196]
	lsr x19, x17, #5
	and x19, x19, x20
	strb w19, [x3, #2197]
	lsr x19, x17, #6
	and x19, x19, x20
	strb w19, [x3, #2198]
	lsr x19, x17, #7
	and x19, x19, x20
	strb w19, [x3, #2199]
	ldrb w17, [x1, #27]
	lsr x19, x17, #0
	and x19, x19, x20
	strb w19, [x3, #2200]
	lsr x19, x17, #1
	and x19, x19, x20
	strb w19, [x3, #2201]
	lsr x19, x17, #2
	and x19, x19, x20
	strb w19, [x3, #2202]
	lsr x19, x17, #3
	and x19, x19, x20
	strb w19, [x3, #2203]
	lsr x19, x17, #4
	and x19, x19, x20
	strb w19, [x3, #2204]
	lsr x19, x17, #5
	and x19, x19, x20
	strb w19, [x3, #2205]
	lsr x19, x17, #6
	and x19, x19, x20
	strb w19, [x3, #2206]
	lsr x19, x17, #7
	and x19, x19, x20
	strb w19, [x3, #2207]
	ldrb w17, [x1, #28]
	lsr x19, x17, #0
	and x19, x19, x20
	strb w19, [x3, #2208]
	lsr x19, x17, #1
	and x19, x19, x20
	strb w19, [x3, #2209]
	lsr x19, x17, #2
	and x19, x19, x20
	strb w19, [x3, #2210]
	lsr x19, x17, #3
	and x19, x19, x20
	strb w19, [x3, #2211]
	lsr x19, x17, #4
	and x19, x19, x20
	strb w19, [x3, #2212]
	lsr x19, x17, #5
	and x19, x19, x20
	strb w19, [x3, #2213]
	lsr x19, x17, #6
	and x19, x19, x20
	strb w19, [x3, #2214]
	lsr x19, x17, #7
	and x19, x19, x20
	strb w19, [x3, #2215]
	ldrb w17, [x1, #29]
	lsr x19, x17, #0
	and x19, x19, x20
	strb w19, [x3, #2216]
	lsr x19, x17, #1
	and x19, x19, x20
	strb w19, [x3, #2217]
	lsr x19, x17, #2
	and x19, x19, x20
	strb w19, [x3, #2218]
	lsr x19, x17, #3
	and x19, x19, x20
	strb w19, [x3, #2219]
	lsr x19, x17, #4
	and x19, x19, x20
	strb w19, [x3, #2220]
	lsr x19, x17, #5
	and x19, x19, x20
	strb w19, [x3, #2221]
	lsr x19, x17, #6
	and x19, x19, x20
	strb w19, [x3, #2222]
	lsr x19, x17, #7
	and x19, x19, x20
	strb w19, [x3, #2223]
	ldrb w17, [x1, #30]
	lsr x19, x17, #0
	and x19, x19, x20
	strb w19, [x3, #2224]
	lsr x19, x17, #1
	and x19, x19, x20
	strb w19, [x3, #2225]
	lsr x19, x17, #2
	and x19, x19, x20
	strb w19, [x3, #2226]
	lsr x19, x17, #3
	and x19, x19, x20
	strb w19, [x3, #2227]
	lsr x19, x17, #4
	and x19, x19, x20
	strb w19, [x3, #2228]
	lsr x19, x17, #5
	and x19, x19, x20
	strb w19, [x3, #2229]
	lsr x19, x17, #6
	and x19, x19, x20
	strb w19, [x3, #2230]
	lsr x19, x17, #7
	and x19, x19, x20
	strb w19, [x3, #2231]
	ldrb w17, [x1, #31]
	lsr x19, x17, #0
	and x19, x19, x20
	strb w19, [x3, #2232]
	lsr x19, x17, #1
	and x19, x19, x20
	strb w19, [x3, #2233]
	lsr x19, x17, #2
	and x19, x19, x20
	strb w19, [x3, #2234]
	lsr x19, x17, #3
	and x19, x19, x20
	strb w19, [x3, #2235]
	lsr x19, x17, #4
	and x19, x19, x20
	strb w19, [x3, #2236]
	lsr x19, x17, #5
	and x19, x19, x20
	strb w19, [x3, #2237]
	lsr x19, x17, #6
	and x19, x19, x20
	strb w19, [x3, #2238]
	lsr x19, x17, #7
	and x19, x19, x20
	strb w19, [x3, #2239]
	movz x19, #0, lsl #0
	strb w19, [x3, #1984]
	strb w19, [x3, #1985]
	strb w19, [x3, #1986]
	strb w20, [x3, #2238]
	str x0, [x3, #48]
	add x1, x0, #0
	add x0, x3, #0
	ldr x4, [x2, #0]
	ldr x5, [x2, #8]
	ldr x6, [x2, #16]
	ldr x7, [x2, #24]
	movz x8, #65535, lsl #0
	movk x8, #65535, lsl #16
	movk x8, #65535, lsl #32
	movk x8, #32767, lsl #48
	and x7, x7, x8
	str x4, [x0, #64]
	str x5, [x0, #72]
	str x6, [x0, #80]
	str x7, [x0, #88]
	ldr x4, [x0, #64]
	ldr x5, [x0, #72]
	ldr x6, [x0, #80]
	ldr x7, [x0, #88]
	str x4, [x0, #160]
	str x5, [x0, #168]
	str x6, [x0, #176]
	str x7, [x0, #184]
	movz x4, #1, lsl #0
	movk x4, #0, lsl #16
	movk x4, #0, lsl #32
	movk x4, #0, lsl #48
	movz x5, #0, lsl #0
	movk x5, #0, lsl #16
	movk x5, #0, lsl #32
	movk x5, #0, lsl #48
	movz x6, #0, lsl #0
	movk x6, #0, lsl #16
	movk x6, #0, lsl #32
	movk x6, #0, lsl #48
	movz x7, #0, lsl #0
	movk x7, #0, lsl #16
	movk x7, #0, lsl #32
	movk x7, #0, lsl #48
	str x4, [x0, #96]
	str x5, [x0, #104]
	str x6, [x0, #112]
	str x7, [x0, #120]
	movz x4, #0, lsl #0
	movk x4, #0, lsl #16
	movk x4, #0, lsl #32
	movk x4, #0, lsl #48
	movz x5, #0, lsl #0
	movk x5, #0, lsl #16
	movk x5, #0, lsl #32
	movk x5, #0, lsl #48
	movz x6, #0, lsl #0
	movk x6, #0, lsl #16
	movk x6, #0, lsl #32
	movk x6, #0, lsl #48
	movz x7, #0, lsl #0
	movk x7, #0, lsl #16
	movk x7, #0, lsl #32
	movk x7, #0, lsl #48
	str x4, [x0, #128]
	str x5, [x0, #136]
	str x6, [x0, #144]
	str x7, [x0, #152]
	movz x4, #1, lsl #0
	movk x4, #0, lsl #16
	movk x4, #0, lsl #32
	movk x4, #0, lsl #48
	movz x5, #0, lsl #0
	movk x5, #0, lsl #16
	movk x5, #0, lsl #32
	movk x5, #0, lsl #48
	movz x6, #0, lsl #0
	movk x6, #0, lsl #16
	movk x6, #0, lsl #32
	movk x6, #0, lsl #48
	movz x7, #0, lsl #0
	movk x7, #0, lsl #16
	movk x7, #0, lsl #32
	movk x7, #0, lsl #48
	str x4, [x0, #192]
	str x5, [x0, #200]
	str x6, [x0, #208]
	str x7, [x0, #216]
	movz x4, #56129, lsl #0
	movk x4, #1, lsl #16
	movk x4, #0, lsl #32
	movk x4, #0, lsl #48
	movz x5, #0, lsl #0
	movk x5, #0, lsl #16
	movk x5, #0, lsl #32
	movk x5, #0, lsl #48
	movz x6, #0, lsl #0
	movk x6, #0, lsl #16
	movk x6, #0, lsl #32
	movk x6, #0, lsl #48
	movz x7, #0, lsl #0
	movk x7, #0, lsl #16
	movk x7, #0, lsl #32
	movk x7, #0, lsl #48
	str x4, [x0, #640]
	str x5, [x0, #648]
	str x6, [x0, #656]
	str x7, [x0, #664]
	movz x2, #0, lsl #0
	str x2, [x0, #768]
	movz x17, #0, lsl #0
	ldp x5, x6, [x0, #160]
	ldp x4, x3, [x0, #192]
	subs x5, x5, x4
	sbcs x6, x6, x3
	ldp x7, x8, [x0, #176]
	ldp x4, x3, [x0, #208]
	sbcs x7, x7, x4
	sbcs x8, x8, x3
	movz w4, #38, lsl #0
	csel x3, x4, x17, lo
	subs x5, x5, x3
	sbcs x6, x6, x17
	sbcs x7, x7, x17
	sbc x8, x8, x17
	stp x5, x6, [x0, #320]
	stp x7, x8, [x0, #336]
	ldp x3, x4, [x0, #160]
	ldp x7, x8, [x0, #192]
	adds x3, x3, x7
	adcs x4, x4, x8
	ldp x5, x6, [x0, #176]
	ldp x7, x8, [x0, #208]
	adcs x5, x5, x7
	adcs x6, x6, x8
	movz w9, #38, lsl #0
	csel x9, x9, x17, hs
	adds x3, x3, x9
	adcs x4, x4, x17
	adcs x5, x5, x17
	adc x6, x6, x17
	stp x3, x4, [x0, #96]
	stp x5, x6, [x0, #112]
	add x20, x1, #0
	movz x1, #4, lsl #0
	ldp x7, x8, [x0, #64]
	ldp x9, x10, [x0, #80]
	mul x3, x1, x7
	mul x4, x1, x8
	mul x5, x1, x9
	mul x6, x1, x10
	umulh x7, x1, x7
	umulh x8, x1, x8
	umulh x9, x1, x9
	umulh x10, x1, x10
	adds x4, x4, x7
	adcs x5, x5, x8
	adcs x6, x6, x9
	adc x10, x10, x17
	ldp x7, x8, [x0, #128]
	adds x3, x3, x7
	adcs x4, x4, x8
	ldp x7, x8, [x0, #144]
	adcs x5, x5, x7
	adcs x6, x6, x8
	adc x10, x10, x17
	adds x7, x6, x6
	lsr x6, x7, #1
	adc x8, x10, x10
	movz w9, #19, lsl #0
	mul x7, x8, x9
	adds x3, x3, x7
	adcs x4, x4, x17
	adcs x5, x5, x17
	adc x6, x6, x17
	stp x3, x4, [x0, #192]
	stp x5, x6, [x0, #208]
	add x1, x20, #0
	ldp x2, x3, [x0, #320]
	mul x9, x2, x3
	umulh x10, x2, x3
	ldp x4, x5, [x0, #336]
	mul x11, x2, x5
	umulh x12, x2, x5
	mul x7, x2, x4
	umulh x6, x2, x4
	adds x10, x10, x7
	adcs x11, x11, x6
	mul x7, x3, x4
	umulh x6, x3, x4
	adc x6, x6, x17
	adds x11, x11, x7
	mul x13, x4, x5
	umulh x14, x4, x5
	adcs x12, x12, x6
	mul x7, x3, x5
	umulh x6, x3, x5
	adc x6, x6, x17
	adds x12, x12, x7
	adcs x13, x13, x6
	adc x14, x14, x17
	adds x9, x9, x9
	adcs x10, x10, x10
	adcs x11, x11, x11
	adcs x12, x12, x12
	adcs x13, x13, x13
	adcs x14, x14, x14
	adc x6, x17, x17
	umulh x7, x2, x2
	mul x8, x2, x2
	adds x9, x9, x7
	mul x7, x3, x3
	adcs x10, x10, x7
	umulh x7, x3, x3
	adcs x11, x11, x7
	mul x7, x4, x4
	adcs x12, x12, x7
	umulh x7, x4, x4
	adcs x13, x13, x7
	mul x7, x5, x5
	adcs x14, x14, x7
	umulh x7, x5, x5
	adc x6, x6, x7
	movz w3, #38, lsl #0
	mul x7, x3, x12
	umulh x4, x3, x12
	adds x8, x8, x7
	mul x7, x3, x13
	umulh x13, x3, x13
	adcs x9, x9, x7
	mul x7, x3, x14
	umulh x14, x3, x14
	adcs x10, x10, x7
	mul x7, x3, x6
	umulh x6, x3, x6
	adcs x11, x11, x7
	adc x12, x17, x17
	adds x11, x11, x14
	adc x12, x12, x6
	adds x7, x11, x11
	lsr x11, x7, #1
	adc x2, x12, x12
	movz w3, #19, lsl #0
	mul x7, x3, x2
	adds x8, x8, x7
	adcs x9, x9, x4
	adcs x10, x10, x13
	adc x11, x11, x17
	stp x8, x9, [x0, #320]
	stp x10, x11, [x0, #336]
	ldp x2, x3, [x0, #96]
	mul x9, x2, x3
	umulh x10, x2, x3
	ldp x4, x5, [x0, #112]
	mul x11, x2, x5
	umulh x12, x2, x5
	mul x7, x2, x4
	umulh x6, x2, x4
	adds x10, x10, x7
	adcs x11, x11, x6
	mul x7, x3, x4
	umulh x6, x3, x4
	adc x6, x6, x17
	adds x11, x11, x7
	mul x13, x4, x5
	umulh x14, x4, x5
	adcs x12, x12, x6
	mul x7, x3, x5
	umulh x6, x3, x5
	adc x6, x6, x17
	adds x12, x12, x7
	adcs x13, x13, x6
	adc x14, x14, x17
	adds x9, x9, x9
	adcs x10, x10, x10
	adcs x11, x11, x11
	adcs x12, x12, x12
	adcs x13, x13, x13
	adcs x14, x14, x14
	adc x6, x17, x17
	umulh x7, x2, x2
	mul x8, x2, x2
	adds x9, x9, x7
	mul x7, x3, x3
	adcs x10, x10, x7
	umulh x7, x3, x3
	adcs x11, x11, x7
	mul x7, x4, x4
	adcs x12, x12, x7
	umulh x7, x4, x4
	adcs x13, x13, x7
	mul x7, x5, x5
	adcs x14, x14, x7
	umulh x7, x5, x5
	adc x6, x6, x7
	movz w3, #38, lsl #0
	mul x7, x3, x12
	umulh x4, x3, x12
	adds x8, x8, x7
	mul x7, x3, x13
	umulh x13, x3, x13
	adcs x9, x9, x7
	mul x7, x3, x14
	umulh x14, x3, x14
	adcs x10, x10, x7
	mul x7, x3, x6
	umulh x6, x3, x6
	adcs x11, x11, x7
	adc x12, x17, x17
	adds x11, x11, x14
	adc x12, x12, x6
	adds x7, x11, x11
	lsr x11, x7, #1
	adc x2, x12, x12
	movz w3, #19, lsl #0
	mul x7, x3, x2
	adds x8, x8, x7
	adcs x9, x9, x4
	adcs x10, x10, x13
	adc x11, x11, x17
	stp x8, x9, [x0, #96]
	stp x10, x11, [x0, #112]
	ldp x3, x4, [x0, #64]
	ldp x7, x8, [x0, #192]
	mul x12, x3, x7
	umulh x13, x3, x7
	mul x11, x3, x8
	umulh x14, x3, x8
	adds x13, x13, x11
	ldp x9, x10, [x0, #208]
	mul x11, x3, x9
	umulh x15, x3, x9
	adcs x14, x14, x11
	mul x11, x3, x10
	umulh x16, x3, x10
	adcs x15, x15, x11
	adc x16, x16, x17
	ldp x5, x6, [x0, #80]
	mul x11, x4, x7
	adds x13, x13, x11
	mul x11, x4, x8
	adcs x14, x14, x11
	mul x11, x4, x9
	adcs x15, x15, x11
	mul x11, x4, x10
	adcs x16, x16, x11
	umulh x3, x4, x10
	adc x3, x3, x17
	umulh x11, x4, x7
	adds x14, x14, x11
	umulh x11, x4, x8
	adcs x15, x15, x11
	umulh x11, x4, x9
	adcs x16, x16, x11
	adc x3, x3, x17
	mul x11, x5, x7
	adds x14, x14, x11
	mul x11, x5, x8
	adcs x15, x15, x11
	mul x11, x5, x9
	adcs x16, x16, x11
	mul x11, x5, x10
	adcs x3, x3, x11
	umulh x4, x5, x10
	adc x4, x4, x17
	umulh x11, x5, x7
	adds x15, x15, x11
	umulh x11, x5, x8
	adcs x16, x16, x11
	umulh x11, x5, x9
	adcs x3, x3, x11
	adc x4, x4, x17
	mul x11, x6, x7
	adds x15, x15, x11
	mul x11, x6, x8
	adcs x16, x16, x11
	mul x11, x6, x9
	adcs x3, x3, x11
	mul x11, x6, x10
	adcs x4, x4, x11
	umulh x5, x6, x10
	adc x5, x5, x17
	umulh x11, x6, x7
	adds x16, x16, x11
	umulh x11, x6, x8
	adcs x3, x3, x11
	umulh x11, x6, x9
	adcs x4, x4, x11
	adc x5, x5, x17
	movz w7, #38, lsl #0
	mul x11, x7, x16
	umulh x9, x7, x16
	adds x12, x12, x11
	mul x11, x7, x3
	umulh x3, x7, x3
	adcs x13, x13, x11
	mul x11, x7, x4
	umulh x4, x7, x4
	adcs x14, x14, x11
	mul x11, x7, x5
	umulh x5, x7, x5
	adcs x15, x15, x11
	adc x16, x17, x17
	adds x15, x15, x4
	adc x16, x16, x5
	adds x11, x15, x15
	lsr x15, x11, #1
	adc x8, x16, x16
	movz w7, #19, lsl #0
	mul x11, x7, x8
	adds x12, x12, x11
	adcs x13, x13, x9
	adcs x14, x14, x3
	adc x15, x15, x17
	stp x12, x13, [x0, #160]
	stp x14, x15, [x0, #176]
	ldp x5, x6, [x0, #96]
	ldp x4, x3, [x0, #320]
	subs x5, x5, x4
	sbcs x6, x6, x3
	ldp x7, x8, [x0, #112]
	ldp x4, x3, [x0, #336]
	sbcs x7, x7, x4
	sbcs x8, x8, x3
	movz w4, #38, lsl #0
	csel x3, x4, x17, lo
	subs x5, x5, x3
	sbcs x6, x6, x17
	sbcs x7, x7, x17
	sbc x8, x8, x17
	stp x5, x6, [x0, #288]
	stp x7, x8, [x0, #304]
	add x20, x1, #0
	movz x1, #56130, lsl #0
	movk x1, #1, lsl #16
	ldp x7, x8, [x0, #288]
	ldp x9, x10, [x0, #304]
	mul x3, x1, x7
	mul x4, x1, x8
	mul x5, x1, x9
	mul x6, x1, x10
	umulh x7, x1, x7
	umulh x8, x1, x8
	umulh x9, x1, x9
	umulh x10, x1, x10
	adds x4, x4, x7
	adcs x5, x5, x8
	adcs x6, x6, x9
	adc x10, x10, x17
	ldp x7, x8, [x0, #320]
	adds x3, x3, x7
	adcs x4, x4, x8
	ldp x7, x8, [x0, #336]
	adcs x5, x5, x7
	adcs x6, x6, x8
	adc x10, x10, x17
	adds x7, x6, x6
	lsr x6, x7, #1
	adc x8, x10, x10
	movz w9, #19, lsl #0
	mul x7, x8, x9
	adds x3, x3, x7
	adcs x4, x4, x17
	adcs x5, x5, x17
	adc x6, x6, x17
	stp x3, x4, [x0, #128]
	stp x5, x6, [x0, #144]
	add x1, x20, #0
	ldp x3, x4, [x0, #96]
	ldp x7, x8, [x0, #320]
	mul x12, x3, x7
	umulh x13, x3, x7
	mul x11, x3, x8
	umulh x14, x3, x8
	adds x13, x13, x11
	ldp x9, x10, [x0, #336]
	mul x11, x3, x9
	umulh x15, x3, x9
	adcs x14, x14, x11
	mul x11, x3, x10
	umulh x16, x3, x10
	adcs x15, x15, x11
	adc x16, x16, x17
	ldp x5, x6, [x0, #112]
	mul x11, x4, x7
	adds x13, x13, x11
	mul x11, x4, x8
	adcs x14, x14, x11
	mul x11, x4, x9
	adcs x15, x15, x11
	mul x11, x4, x10
	adcs x16, x16, x11
	umulh x3, x4, x10
	adc x3, x3, x17
	umulh x11, x4, x7
	adds x14, x14, x11
	umulh x11, x4, x8
	adcs x15, x15, x11
	umulh x11, x4, x9
	adcs x16, x16, x11
	adc x3, x3, x17
	mul x11, x5, x7
	adds x14, x14, x11
	mul x11, x5, x8
	adcs x15, x15, x11
	mul x11, x5, x9
	adcs x16, x16, x11
	mul x11, x5, x10
	adcs x3, x3, x11
	umulh x4, x5, x10
	adc x4, x4, x17
	umulh x11, x5, x7
	adds x15, x15, x11
	umulh x11, x5, x8
	adcs x16, x16, x11
	umulh x11, x5, x9
	adcs x3, x3, x11
	adc x4, x4, x17
	mul x11, x6, x7
	adds x15, x15, x11
	mul x11, x6, x8
	adcs x16, x16, x11
	mul x11, x6, x9
	adcs x3, x3, x11
	mul x11, x6, x10
	adcs x4, x4, x11
	umulh x5, x6, x10
	adc x5, x5, x17
	umulh x11, x6, x7
	adds x16, x16, x11
	umulh x11, x6, x8
	adcs x3, x3, x11
	umulh x11, x6, x9
	adcs x4, x4, x11
	adc x5, x5, x17
	movz w7, #38, lsl #0
	mul x11, x7, x16
	umulh x9, x7, x16
	adds x12, x12, x11
	mul x11, x7, x3
	umulh x3, x7, x3
	adcs x13, x13, x11
	mul x11, x7, x4
	umulh x4, x7, x4
	adcs x14, x14, x11
	mul x11, x7, x5
	umulh x5, x7, x5
	adcs x15, x15, x11
	adc x16, x17, x17
	adds x15, x15, x4
	adc x16, x16, x5
	adds x11, x15, x15
	lsr x15, x11, #1
	adc x8, x16, x16
	movz w7, #19, lsl #0
	mul x11, x7, x8
	adds x12, x12, x11
	adcs x13, x13, x9
	adcs x14, x14, x3
	adc x15, x15, x17
	stp x12, x13, [x0, #96]
	stp x14, x15, [x0, #112]
	ldp x3, x4, [x0, #288]
	ldp x7, x8, [x0, #128]
	mul x12, x3, x7
	umulh x13, x3, x7
	mul x11, x3, x8
	umulh x14, x3, x8
	adds x13, x13, x11
	ldp x9, x10, [x0, #144]
	mul x11, x3, x9
	umulh x15, x3, x9
	adcs x14, x14, x11
	mul x11, x3, x10
	umulh x16, x3, x10
	adcs x15, x15, x11
	adc x16, x16, x17
	ldp x5, x6, [x0, #304]
	mul x11, x4, x7
	adds x13, x13, x11
	mul x11, x4, x8
	adcs x14, x14, x11
	mul x11, x4, x9
	adcs x15, x15, x11
	mul x11, x4, x10
	adcs x16, x16, x11
	umulh x3, x4, x10
	adc x3, x3, x17
	umulh x11, x4, x7
	adds x14, x14, x11
	umulh x11, x4, x8
	adcs x15, x15, x11
	umulh x11, x4, x9
	adcs x16, x16, x11
	adc x3, x3, x17
	mul x11, x5, x7
	adds x14, x14, x11
	mul x11, x5, x8
	adcs x15, x15, x11
	mul x11, x5, x9
	adcs x16, x16, x11
	mul x11, x5, x10
	adcs x3, x3, x11
	umulh x4, x5, x10
	adc x4, x4, x17
	umulh x11, x5, x7
	adds x15, x15, x11
	umulh x11, x5, x8
	adcs x16, x16, x11
	umulh x11, x5, x9
	adcs x3, x3, x11
	adc x4, x4, x17
	mul x11, x6, x7
	adds x15, x15, x11
	mul x11, x6, x8
	adcs x16, x16, x11
	mul x11, x6, x9
	adcs x3, x3, x11
	mul x11, x6, x10
	adcs x4, x4, x11
	umulh x5, x6, x10
	adc x5, x5, x17
	umulh x11, x6, x7
	adds x16, x16, x11
	umulh x11, x6, x8
	adcs x3, x3, x11
	umulh x11, x6, x9
	adcs x4, x4, x11
	adc x5, x5, x17
	movz w7, #38, lsl #0
	mul x11, x7, x16
	umulh x9, x7, x16
	adds x12, x12, x11
	mul x11, x7, x3
	umulh x3, x7, x3
	adcs x13, x13, x11
	mul x11, x7, x4
	umulh x4, x7, x4
	adcs x14, x14, x11
	mul x11, x7, x5
	umulh x5, x7, x5
	adcs x15, x15, x11
	adc x16, x17, x17
	adds x15, x15, x4
	adc x16, x16, x5
	adds x11, x15, x15
	lsr x15, x11, #1
	adc x8, x16, x16
	movz w7, #19, lsl #0
	mul x11, x7, x8
	adds x12, x12, x11
	adcs x13, x13, x9
	adcs x14, x14, x3
	adc x15, x15, x17
	stp x12, x13, [x0, #128]
	stp x14, x15, [x0, #144]
	movz x2, #1, lsl #0
	str x2, [x0, #768]
	movz x19, #254, lsl #0
20:
	movz x17, #0, lsl #0
	ldp x5, x6, [x0, #160]
	ldp x4, x3, [x0, #192]
	subs x5, x5, x4
	sbcs x6, x6, x3
	ldp x7, x8, [x0, #176]
	ldp x4, x3, [x0, #208]
	sbcs x7, x7, x4
	sbcs x8, x8, x3
	movz w4, #38, lsl #0
	csel x3, x4, x17, lo
	subs x5, x5, x3
	sbcs x6, x6, x17
	sbcs x7, x7, x17
	sbc x8, x8, x17
	stp x5, x6, [x0, #256]
	stp x7, x8, [x0, #272]
	ldp x3, x4, [x0, #96]
	ldp x7, x8, [x0, #128]
	adds x3, x3, x7
	adcs x4, x4, x8
	ldp x5, x6, [x0, #112]
	ldp x7, x8, [x0, #144]
	adcs x5, x5, x7
	adcs x6, x6, x8
	movz w9, #38, lsl #0
	csel x9, x9, x17, hs
	adds x3, x3, x9
	adcs x4, x4, x17
	adcs x5, x5, x17
	adc x6, x6, x17
	stp x3, x4, [x0, #224]
	stp x5, x6, [x0, #240]
	ldp x5, x6, [x0, #96]
	ldp x4, x3, [x0, #128]
	subs x5, x5, x4
	sbcs x6, x6, x3
	ldp x7, x8, [x0, #112]
	ldp x4, x3, [x0, #144]
	sbcs x7, x7, x4
	sbcs x8, x8, x3
	movz w4, #38, lsl #0
	csel x3, x4, x17, lo
	subs x5, x5, x3
	sbcs x6, x6, x17
	sbcs x7, x7, x17
	sbc x8, x8, x17
	stp x5, x6, [x0, #128]
	stp x7, x8, [x0, #144]
	ldp x3, x4, [x0, #160]
	ldp x7, x8, [x0, #192]
	adds x3, x3, x7
	adcs x4, x4, x8
	ldp x5, x6, [x0, #176]
	ldp x7, x8, [x0, #208]
	adcs x5, x5, x7
	adcs x6, x6, x8
	movz w9, #38, lsl #0
	csel x9, x9, x17, hs
	adds x3, x3, x9
	adcs x4, x4, x17
	adcs x5, x5, x17
	adc x6, x6, x17
	stp x3, x4, [x0, #192]
	stp x5, x6, [x0, #208]
	ldp x3, x4, [x0, #224]
	ldp x7, x8, [x0, #256]
	mul x12, x3, x7
	umulh x13, x3, x7
	mul x11, x3, x8
	umulh x14, x3, x8
	adds x13, x13, x11
	ldp x9, x10, [x0, #272]
	mul x11, x3, x9
	umulh x15, x3, x9
	adcs x14, x14, x11
	mul x11, x3, x10
	umulh x16, x3, x10
	adcs x15, x15, x11
	adc x16, x16, x17
	ldp x5, x6, [x0, #240]
	mul x11, x4, x7
	adds x13, x13, x11
	mul x11, x4, x8
	adcs x14, x14, x11
	mul x11, x4, x9
	adcs x15, x15, x11
	mul x11, x4, x10
	adcs x16, x16, x11
	umulh x3, x4, x10
	adc x3, x3, x17
	umulh x11, x4, x7
	adds x14, x14, x11
	umulh x11, x4, x8
	adcs x15, x15, x11
	umulh x11, x4, x9
	adcs x16, x16, x11
	adc x3, x3, x17
	mul x11, x5, x7
	adds x14, x14, x11
	mul x11, x5, x8
	adcs x15, x15, x11
	mul x11, x5, x9
	adcs x16, x16, x11
	mul x11, x5, x10
	adcs x3, x3, x11
	umulh x4, x5, x10
	adc x4, x4, x17
	umulh x11, x5, x7
	adds x15, x15, x11
	umulh x11, x5, x8
	adcs x16, x16, x11
	umulh x11, x5, x9
	adcs x3, x3, x11
	adc x4, x4, x17
	mul x11, x6, x7
	adds x15, x15, x11
	mul x11, x6, x8
	adcs x16, x16, x11
	mul x11, x6, x9
	adcs x3, x3, x11
	mul x11, x6, x10
	adcs x4, x4, x11
	umulh x5, x6, x10
	adc x5, x5, x17
	umulh x11, x6, x7
	adds x16, x16, x11
	umulh x11, x6, x8
	adcs x3, x3, x11
	umulh x11, x6, x9
	adcs x4, x4, x11
	adc x5, x5, x17
	movz w7, #38, lsl #0
	mul x11, x7, x16
	umulh x9, x7, x16
	adds x12, x12, x11
	mul x11, x7, x3
	umulh x3, x7, x3
	adcs x13, x13, x11
	mul x11, x7, x4
	umulh x4, x7, x4
	adcs x14, x14, x11
	mul x11, x7, x5
	umulh x5, x7, x5
	adcs x15, x15, x11
	adc x16, x17, x17
	adds x15, x15, x4
	adc x16, x16, x5
	adds x11, x15, x15
	lsr x15, x11, #1
	adc x8, x16, x16
	movz w7, #19, lsl #0
	mul x11, x7, x8
	adds x12, x12, x11
	adcs x13, x13, x9
	adcs x14, x14, x3
	adc x15, x15, x17
	stp x12, x13, [x0, #288]
	stp x14, x15, [x0, #304]
	sub x19, x19, #1
	add x8, x0, x19
	ldrb w2, [x8, #1984]
	ldr x3, [x0, #768]
	str x2, [x0, #768]
	subs x3, x3, x2
	ldp x4, x5, [x0, #256]
	ldp x6, x7, [x0, #128]
	csel x4, x4, x6, ne
	csel x5, x5, x7, ne
	stp x4, x5, [x0, #320]
	ldp x4, x5, [x0, #272]
	ldp x6, x7, [x0, #144]
	csel x4, x4, x6, ne
	csel x5, x5, x7, ne
	stp x4, x5, [x0, #336]
	ldp x4, x5, [x0, #192]
	ldp x6, x7, [x0, #224]
	csel x4, x4, x6, ne
	csel x5, x5, x7, ne
	stp x4, x5, [x0, #96]
	ldp x4, x5, [x0, #208]
	ldp x6, x7, [x0, #240]
	csel x4, x4, x6, ne
	csel x5, x5, x7, ne
	stp x4, x5, [x0, #112]
	ldp x3, x4, [x0, #192]
	ldp x7, x8, [x0, #128]
	mul x12, x3, x7
	umulh x13, x3, x7
	mul x11, x3, x8
	umulh x14, x3, x8
	adds x13, x13, x11
	ldp x9, x10, [x0, #144]
	mul x11, x3, x9
	umulh x15, x3, x9
	adcs x14, x14, x11
	mul x11, x3, x10
	umulh x16, x3, x10
	adcs x15, x15, x11
	adc x16, x16, x17
	ldp x5, x6, [x0, #208]
	mul x11, x4, x7
	adds x13, x13, x11
	mul x11, x4, x8
	adcs x14, x14, x11
	mul x11, x4, x9
	adcs x15, x15, x11
	mul x11, x4, x10
	adcs x16, x16, x11
	umulh x3, x4, x10
	adc x3, x3, x17
	umulh x11, x4, x7
	adds x14, x14, x11
	umulh x11, x4, x8
	adcs x15, x15, x11
	umulh x11, x4, x9
	adcs x16, x16, x11
	adc x3, x3, x17
	mul x11, x5, x7
	adds x14, x14, x11
	mul x11, x5, x8
	adcs x15, x15, x11
	mul x11, x5, x9
	adcs x16, x16, x11
	mul x11, x5, x10
	adcs x3, x3, x11
	umulh x4, x5, x10
	adc x4, x4, x17
	umulh x11, x5, x7
	adds x15, x15, x11
	umulh x11, x5, x8
	adcs x16, x16, x11
	umulh x11, x5, x9
	adcs x3, x3, x11
	adc x4, x4, x17
	mul x11, x6, x7
	adds x15, x15, x11
	mul x11, x6, x8
	adcs x16, x16, x11
	mul x11, x6, x9
	adcs x3, x3, x11
	mul x11, x6, x10
	adcs x4, x4, x11
	umulh x5, x6, x10
	adc x5, x5, x17
	umulh x11, x6, x7
	adds x16, x16, x11
	umulh x11, x6, x8
	adcs x3, x3, x11
	umulh x11, x6, x9
	adcs x4, x4, x11
	adc x5, x5, x17
	movz w7, #38, lsl #0
	mul x11, x7, x16
	umulh x9, x7, x16
	adds x12, x12, x11
	mul x11, x7, x3
	umulh x3, x7, x3
	adcs x13, x13, x11
	mul x11, x7, x4
	umulh x4, x7, x4
	adcs x14, x14, x11
	mul x11, x7, x5
	umulh x5, x7, x5
	adcs x15, x15, x11
	adc x16, x17, x17
	adds x15, x15, x4
	adc x16, x16, x5
	adds x11, x15, x15
	lsr x15, x11, #1
	adc x8, x16, x16
	movz w7, #19, lsl #0
	mul x11, x7, x8
	adds x12, x12, x11
	adcs x13, x13, x9
	adcs x14, x14, x3
	adc x15, x15, x17
	stp x12, x13, [x0, #160]
	stp x14, x15, [x0, #176]
	ldp x2, x3, [x0, #320]
	mul x9, x2, x3
	umulh x10, x2, x3
	ldp x4, x5, [x0, #336]
	mul x11, x2, x5
	umulh x12, x2, x5
	mul x7, x2, x4
	umulh x6, x2, x4
	adds x10, x10, x7
	adcs x11, x11, x6
	mul x7, x3, x4
	umulh x6, x3, x4
	adc x6, x6, x17
	adds x11, x11, x7
	mul x13, x4, x5
	umulh x14, x4, x5
	adcs x12, x12, x6
	mul x7, x3, x5
	umulh x6, x3, x5
	adc x6, x6, x17
	adds x12, x12, x7
	adcs x13, x13, x6
	adc x14, x14, x17
	adds x9, x9, x9
	adcs x10, x10, x10
	adcs x11, x11, x11
	adcs x12, x12, x12
	adcs x13, x13, x13
	adcs x14, x14, x14
	adc x6, x17, x17
	umulh x7, x2, x2
	mul x8, x2, x2
	adds x9, x9, x7
	mul x7, x3, x3
	adcs x10, x10, x7
	umulh x7, x3, x3
	adcs x11, x11, x7
	mul x7, x4, x4
	adcs x12, x12, x7
	umulh x7, x4, x4
	adcs x13, x13, x7
	mul x7, x5, x5
	adcs x14, x14, x7
	umulh x7, x5, x5
	adc x6, x6, x7
	movz w3, #38, lsl #0
	mul x7, x3, x12
	umulh x4, x3, x12
	adds x8, x8, x7
	mul x7, x3, x13
	umulh x13, x3, x13
	adcs x9, x9, x7
	mul x7, x3, x14
	umulh x14, x3, x14
	adcs x10, x10, x7
	mul x7, x3, x6
	umulh x6, x3, x6
	adcs x11, x11, x7
	adc x12, x17, x17
	adds x11, x11, x14
	adc x12, x12, x6
	adds x7, x11, x11
	lsr x11, x7, #1
	adc x2, x12, x12
	movz w3, #19, lsl #0
	mul x7, x3, x2
	adds x8, x8, x7
	adcs x9, x9, x4
	adcs x10, x10, x13
	adc x11, x11, x17
	stp x8, x9, [x0, #320]
	stp x10, x11, [x0, #336]
	ldp x5, x6, [x0, #288]
	ldp x4, x3, [x0, #160]
	subs x5, x5, x4
	sbcs x6, x6, x3
	ldp x7, x8, [x0, #304]
	ldp x4, x3, [x0, #176]
	sbcs x7, x7, x4
	sbcs x8, x8, x3
	movz w4, #38, lsl #0
	csel x3, x4, x17, lo
	subs x5, x5, x3
	sbcs x6, x6, x17
	sbcs x7, x7, x17
	sbc x8, x8, x17
	stp x5, x6, [x0, #192]
	stp x7, x8, [x0, #208]
	ldp x2, x3, [x0, #96]
	mul x9, x2, x3
	umulh x10, x2, x3
	ldp x4, x5, [x0, #112]
	mul x11, x2, x5
	umulh x12, x2, x5
	mul x7, x2, x4
	umulh x6, x2, x4
	adds x10, x10, x7
	adcs x11, x11, x6
	mul x7, x3, x4
	umulh x6, x3, x4
	adc x6, x6, x17
	adds x11, x11, x7
	mul x13, x4, x5
	umulh x14, x4, x5
	adcs x12, x12, x6
	mul x7, x3, x5
	umulh x6, x3, x5
	adc x6, x6, x17
	adds x12, x12, x7
	adcs x13, x13, x6
	adc x14, x14, x17
	adds x9, x9, x9
	adcs x10, x10, x10
	adcs x11, x11, x11
	adcs x12, x12, x12
	adcs x13, x13, x13
	adcs x14, x14, x14
	adc x6, x17, x17
	umulh x7, x2, x2
	mul x8, x2, x2
	adds x9, x9, x7
	mul x7, x3, x3
	adcs x10, x10, x7
	umulh x7, x3, x3
	adcs x11, x11, x7
	mul x7, x4, x4
	adcs x12, x12, x7
	umulh x7, x4, x4
	adcs x13, x13, x7
	mul x7, x5, x5
	adcs x14, x14, x7
	umulh x7, x5, x5
	adc x6, x6, x7
	movz w3, #38, lsl #0
	mul x7, x3, x12
	umulh x4, x3, x12
	adds x8, x8, x7
	mul x7, x3, x13
	umulh x13, x3, x13
	adcs x9, x9, x7
	mul x7, x3, x14
	umulh x14, x3, x14
	adcs x10, x10, x7
	mul x7, x3, x6
	umulh x6, x3, x6
	adcs x11, x11, x7
	adc x12, x17, x17
	adds x11, x11, x14
	adc x12, x12, x6
	adds x7, x11, x11
	lsr x11, x7, #1
	adc x2, x12, x12
	movz w3, #19, lsl #0
	mul x7, x3, x2
	adds x8, x8, x7
	adcs x9, x9, x4
	adcs x10, x10, x13
	adc x11, x11, x17
	stp x8, x9, [x0, #96]
	stp x10, x11, [x0, #112]
	ldp x3, x4, [x0, #288]
	ldp x7, x8, [x0, #160]
	adds x3, x3, x7
	adcs x4, x4, x8
	ldp x5, x6, [x0, #304]
	ldp x7, x8, [x0, #176]
	adcs x5, x5, x7
	adcs x6, x6, x8
	movz w9, #38, lsl #0
	csel x9, x9, x17, hs
	adds x3, x3, x9
	adcs x4, x4, x17
	adcs x5, x5, x17
	adc x6, x6, x17
	stp x3, x4, [x0, #160]
	stp x5, x6, [x0, #176]
	ldp x2, x3, [x0, #192]
	mul x9, x2, x3
	umulh x10, x2, x3
	ldp x4, x5, [x0, #208]
	mul x11, x2, x5
	umulh x12, x2, x5
	mul x7, x2, x4
	umulh x6, x2, x4
	adds x10, x10, x7
	adcs x11, x11, x6
	mul x7, x3, x4
	umulh x6, x3, x4
	adc x6, x6, x17
	adds x11, x11, x7
	mul x13, x4, x5
	umulh x14, x4, x5
	adcs x12, x12, x6
	mul x7, x3, x5
	umulh x6, x3, x5
	adc x6, x6, x17
	adds x12, x12, x7
	adcs x13, x13, x6
	adc x14, x14, x17
	adds x9, x9, x9
	adcs x10, x10, x10
	adcs x11, x11, x11
	adcs x12, x12, x12
	adcs x13, x13, x13
	adcs x14, x14, x14
	adc x6, x17, x17
	umulh x7, x2, x2
	mul x8, x2, x2
	adds x9, x9, x7
	mul x7, x3, x3
	adcs x10, x10, x7
	umulh x7, x3, x3
	adcs x11, x11, x7
	mul x7, x4, x4
	adcs x12, x12, x7
	umulh x7, x4, x4
	adcs x13, x13, x7
	mul x7, x5, x5
	adcs x14, x14, x7
	umulh x7, x5, x5
	adc x6, x6, x7
	movz w3, #38, lsl #0
	mul x7, x3, x12
	umulh x4, x3, x12
	adds x8, x8, x7
	mul x7, x3, x13
	umulh x13, x3, x13
	adcs x9, x9, x7
	mul x7, x3, x14
	umulh x14, x3, x14
	adcs x10, x10, x7
	mul x7, x3, x6
	umulh x6, x3, x6
	adcs x11, x11, x7
	adc x12, x17, x17
	adds x11, x11, x14
	adc x12, x12, x6
	adds x7, x11, x11
	lsr x11, x7, #1
	adc x2, x12, x12
	movz w3, #19, lsl #0
	mul x7, x3, x2
	adds x8, x8, x7
	adcs x9, x9, x4
	adcs x10, x10, x13
	adc x11, x11, x17
	stp x8, x9, [x0, #192]
	stp x10, x11, [x0, #208]
	ldp x5, x6, [x0, #96]
	ldp x4, x3, [x0, #320]
	subs x5, x5, x4
	sbcs x6, x6, x3
	ldp x7, x8, [x0, #112]
	ldp x4, x3, [x0, #336]
	sbcs x7, x7, x4
	sbcs x8, x8, x3
	movz w4, #38, lsl #0
	csel x3, x4, x17, lo
	subs x5, x5, x3
	sbcs x6, x6, x17
	sbcs x7, x7, x17
	sbc x8, x8, x17
	stp x5, x6, [x0, #288]
	stp x7, x8, [x0, #304]
	ldp x2, x3, [x0, #160]
	mul x9, x2, x3
	umulh x10, x2, x3
	ldp x4, x5, [x0, #176]
	mul x11, x2, x5
	umulh x12, x2, x5
	mul x7, x2, x4
	umulh x6, x2, x4
	adds x10, x10, x7
	adcs x11, x11, x6
	mul x7, x3, x4
	umulh x6, x3, x4
	adc x6, x6, x17
	adds x11, x11, x7
	mul x13, x4, x5
	umulh x14, x4, x5
	adcs x12, x12, x6
	mul x7, x3, x5
	umulh x6, x3, x5
	adc x6, x6, x17
	adds x12, x12, x7
	adcs x13, x13, x6
	adc x14, x14, x17
	adds x9, x9, x9
	adcs x10, x10, x10
	adcs x11, x11, x11
	adcs x12, x12, x12
	adcs x13, x13, x13
	adcs x14, x14, x14
	adc x6, x17, x17
	umulh x7, x2, x2
	mul x8, x2, x2
	adds x9, x9, x7
	mul x7, x3, x3
	adcs x10, x10, x7
	umulh x7, x3, x3
	adcs x11, x11, x7
	mul x7, x4, x4
	adcs x12, x12, x7
	umulh x7, x4, x4
	adcs x13, x13, x7
	mul x7, x5, x5
	adcs x14, x14, x7
	umulh x7, x5, x5
	adc x6, x6, x7
	movz w3, #38, lsl #0
	mul x7, x3, x12
	umulh x4, x3, x12
	adds x8, x8, x7
	mul x7, x3, x13
	umulh x13, x3, x13
	adcs x9, x9, x7
	mul x7, x3, x14
	umulh x14, x3, x14
	adcs x10, x10, x7
	mul x7, x3, x6
	umulh x6, x3, x6
	adcs x11, x11, x7
	adc x12, x17, x17
	adds x11, x11, x14
	adc x12, x12, x6
	adds x7, x11, x11
	lsr x11, x7, #1
	adc x2, x12, x12
	movz w3, #19, lsl #0
	mul x7, x3, x2
	adds x8, x8, x7
	adcs x9, x9, x4
	adcs x10, x10, x13
	adc x11, x11, x17
	stp x8, x9, [x0, #160]
	stp x10, x11, [x0, #176]
	add x20, x1, #0
	movz x1, #56130, lsl #0
	movk x1, #1, lsl #16
	ldp x7, x8, [x0, #288]
	ldp x9, x10, [x0, #304]
	mul x3, x1, x7
	mul x4, x1, x8
	mul x5, x1, x9
	mul x6, x1, x10
	umulh x7, x1, x7
	umulh x8, x1, x8
	umulh x9, x1, x9
	umulh x10, x1, x10
	adds x4, x4, x7
	adcs x5, x5, x8
	adcs x6, x6, x9
	adc x10, x10, x17
	ldp x7, x8, [x0, #320]
	adds x3, x3, x7
	adcs x4, x4, x8
	ldp x7, x8, [x0, #336]
	adcs x5, x5, x7
	adcs x6, x6, x8
	adc x10, x10, x17
	adds x7, x6, x6
	lsr x6, x7, #1
	adc x8, x10, x10
	movz w9, #19, lsl #0
	mul x7, x8, x9
	adds x3, x3, x7
	adcs x4, x4, x17
	adcs x5, x5, x17
	adc x6, x6, x17
	stp x3, x4, [x0, #128]
	stp x5, x6, [x0, #144]
	add x1, x20, #0
	ldp x3, x4, [x0, #96]
	ldp x7, x8, [x0, #320]
	mul x12, x3, x7
	umulh x13, x3, x7
	mul x11, x3, x8
	umulh x14, x3, x8
	adds x13, x13, x11
	ldp x9, x10, [x0, #336]
	mul x11, x3, x9
	umulh x15, x3, x9
	adcs x14, x14, x11
	mul x11, x3, x10
	umulh x16, x3, x10
	adcs x15, x15, x11
	adc x16, x16, x17
	ldp x5, x6, [x0, #112]
	mul x11, x4, x7
	adds x13, x13, x11
	mul x11, x4, x8
	adcs x14, x14, x11
	mul x11, x4, x9
	adcs x15, x15, x11
	mul x11, x4, x10
	adcs x16, x16, x11
	umulh x3, x4, x10
	adc x3, x3, x17
	umulh x11, x4, x7
	adds x14, x14, x11
	umulh x11, x4, x8
	adcs x15, x15, x11
	umulh x11, x4, x9
	adcs x16, x16, x11
	adc x3, x3, x17
	mul x11, x5, x7
	adds x14, x14, x11
	mul x11, x5, x8
	adcs x15, x15, x11
	mul x11, x5, x9
	adcs x16, x16, x11
	mul x11, x5, x10
	adcs x3, x3, x11
	umulh x4, x5, x10
	adc x4, x4, x17
	umulh x11, x5, x7
	adds x15, x15, x11
	umulh x11, x5, x8
	adcs x16, x16, x11
	umulh x11, x5, x9
	adcs x3, x3, x11
	adc x4, x4, x17
	mul x11, x6, x7
	adds x15, x15, x11
	mul x11, x6, x8
	adcs x16, x16, x11
	mul x11, x6, x9
	adcs x3, x3, x11
	mul x11, x6, x10
	adcs x4, x4, x11
	umulh x5, x6, x10
	adc x5, x5, x17
	umulh x11, x6, x7
	adds x16, x16, x11
	umulh x11, x6, x8
	adcs x3, x3, x11
	umulh x11, x6, x9
	adcs x4, x4, x11
	adc x5, x5, x17
	movz w7, #38, lsl #0
	mul x11, x7, x16
	umulh x9, x7, x16
	adds x12, x12, x11
	mul x11, x7, x3
	umulh x3, x7, x3
	adcs x13, x13, x11
	mul x11, x7, x4
	umulh x4, x7, x4
	adcs x14, x14, x11
	mul x11, x7, x5
	umulh x5, x7, x5
	adcs x15, x15, x11
	adc x16, x17, x17
	adds x15, x15, x4
	adc x16, x16, x5
	adds x11, x15, x15
	lsr x15, x11, #1
	adc x8, x16, x16
	movz w7, #19, lsl #0
	mul x11, x7, x8
	adds x12, x12, x11
	adcs x13, x13, x9
	adcs x14, x14, x3
	adc x15, x15, x17
	stp x12, x13, [x0, #96]
	stp x14, x15, [x0, #112]
	ldp x3, x4, [x0, #192]
	ldp x7, x8, [x0, #64]
	mul x12, x3, x7
	umulh x13, x3, x7
	mul x11, x3, x8
	umulh x14, x3, x8
	adds x13, x13, x11
	ldp x9, x10, [x0, #80]
	mul x11, x3, x9
	umulh x15, x3, x9
	adcs x14, x14, x11
	mul x11, x3, x10
	umulh x16, x3, x10
	adcs x15, x15, x11
	adc x16, x16, x17
	ldp x5, x6, [x0, #208]
	mul x11, x4, x7
	adds x13, x13, x11
	mul x11, x4, x8
	adcs x14, x14, x11
	mul x11, x4, x9
	adcs x15, x15, x11
	mul x11, x4, x10
	adcs x16, x16, x11
	umulh x3, x4, x10
	adc x3, x3, x17
	umulh x11, x4, x7
	adds x14, x14, x11
	umulh x11, x4, x8
	adcs x15, x15, x11
	umulh x11, x4, x9
	adcs x16, x16, x11
	adc x3, x3, x17
	mul x11, x5, x7
	adds x14, x14, x11
	mul x11, x5, x8
	adcs x15, x15, x11
	mul x11, x5, x9
	adcs x16, x16, x11
	mul x11, x5, x10
	adcs x3, x3, x11
	umulh x4, x5, x10
	adc x4, x4, x17
	umulh x11, x5, x7
	adds x15, x15, x11
	umulh x11, x5, x8
	adcs x16, x16, x11
	umulh x11, x5, x9
	adcs x3, x3, x11
	adc x4, x4, x17
	mul x11, x6, x7
	adds x15, x15, x11
	mul x11, x6, x8
	adcs x16, x16, x11
	mul x11, x6, x9
	adcs x3, x3, x11
	mul x11, x6, x10
	adcs x4, x4, x11
	umulh x5, x6, x10
	adc x5, x5, x17
	umulh x11, x6, x7
	adds x16, x16, x11
	umulh x11, x6, x8
	adcs x3, x3, x11
	umulh x11, x6, x9
	adcs x4, x4, x11
	adc x5, x5, x17
	movz w7, #38, lsl #0
	mul x11, x7, x16
	umulh x9, x7, x16
	adds x12, x12, x11
	mul x11, x7, x3
	umulh x3, x7, x3
	adcs x13, x13, x11
	mul x11, x7, x4
	umulh x4, x7, x4
	adcs x14, x14, x11
	mul x11, x7, x5
	umulh x5, x7, x5
	adcs x15, x15, x11
	adc x16, x17, x17
	adds x15, x15, x4
	adc x16, x16, x5
	adds x11, x15, x15
	lsr x15, x11, #1
	adc x8, x16, x16
	movz w7, #19, lsl #0
	mul x11, x7, x8
	adds x12, x12, x11
	adcs x13, x13, x9
	adcs x14, x14, x3
	adc x15, x15, x17
	stp x12, x13, [x0, #192]
	stp x14, x15, [x0, #208]
	ldp x3, x4, [x0, #288]
	ldp x7, x8, [x0, #128]
	mul x12, x3, x7
	umulh x13, x3, x7
	mul x11, x3, x8
	umulh x14, x3, x8
	adds x13, x13, x11
	ldp x9, x10, [x0, #144]
	mul x11, x3, x9
	umulh x15, x3, x9
	adcs x14, x14, x11
	mul x11, x3, x10
	umulh x16, x3, x10
	adcs x15, x15, x11
	adc x16, x16, x17
	ldp x5, x6, [x0, #304]
	mul x11, x4, x7
	adds x13, x13, x11
	mul x11, x4, x8
	adcs x14, x14, x11
	mul x11, x4, x9
	adcs x15, x15, x11
	mul x11, x4, x10
	adcs x16, x16, x11
	umulh x3, x4, x10
	adc x3, x3, x17
	umulh x11, x4, x7
	adds x14, x14, x11
	umulh x11, x4, x8
	adcs x15, x15, x11
	umulh x11, x4, x9
	adcs x16, x16, x11
	adc x3, x3, x17
	mul x11, x5, x7
	adds x14, x14, x11
	mul x11, x5, x8
	adcs x15, x15, x11
	mul x11, x5, x9
	adcs x16, x16, x11
	mul x11, x5, x10
	adcs x3, x3, x11
	umulh x4, x5, x10
	adc x4, x4, x17
	umulh x11, x5, x7
	adds x15, x15, x11
	umulh x11, x5, x8
	adcs x16, x16, x11
	umulh x11, x5, x9
	adcs x3, x3, x11
	adc x4, x4, x17
	mul x11, x6, x7
	adds x15, x15, x11
	mul x11, x6, x8
	adcs x16, x16, x11
	mul x11, x6, x9
	adcs x3, x3, x11
	mul x11, x6, x10
	adcs x4, x4, x11
	umulh x5, x6, x10
	adc x5, x5, x17
	umulh x11, x6, x7
	adds x16, x16, x11
	umulh x11, x6, x8
	adcs x3, x3, x11
	umulh x11, x6, x9
	adcs x4, x4, x11
	adc x5, x5, x17
	movz w7, #38, lsl #0
	mul x11, x7, x16
	umulh x9, x7, x16
	adds x12, x12, x11
	mul x11, x7, x3
	umulh x3, x7, x3
	adcs x13, x13, x11
	mul x11, x7, x4
	umulh x4, x7, x4
	adcs x14, x14, x11
	mul x11, x7, x5
	umulh x5, x7, x5
	adcs x15, x15, x11
	adc x16, x17, x17
	adds x15, x15, x4
	adc x16, x16, x5
	adds x11, x15, x15
	lsr x15, x11, #1
	adc x8, x16, x16
	movz w7, #19, lsl #0
	mul x11, x7, x8
	adds x12, x12, x11
	adcs x13, x13, x9
	adcs x14, x14, x3
	adc x15, x15, x17
	stp x12, x13, [x0, #128]
	stp x14, x15, [x0, #144]
	sub x16, x19, #3
	cbnz x16, 20b
	movz x17, #0, lsl #0
	ldr x3, [x0, #768]
	movz x2, #0, lsl #0
	subs x3, x3, x2
	ldp x4, x5, [x0, #160]
	ldp x6, x7, [x0, #96]
	csel x4, x4, x6, ne
	csel x5, x5, x7, ne
	stp x4, x5, [x0, #96]
	ldp x4, x5, [x0, #176]
	ldp x6, x7, [x0, #112]
	csel x4, x4, x6, ne
	csel x5, x5, x7, ne
	stp x4, x5, [x0, #112]
	ldp x4, x5, [x0, #192]
	ldp x6, x7, [x0, #128]
	csel x4, x4, x6, ne
	csel x5, x5, x7, ne
	stp x4, x5, [x0, #128]
	ldp x4, x5, [x0, #208]
	ldp x6, x7, [x0, #144]
	csel x4, x4, x6, ne
	csel x5, x5, x7, ne
	stp x4, x5, [x0, #144]
	ldp x5, x6, [x0, #96]
	ldp x4, x3, [x0, #128]
	subs x5, x5, x4
	sbcs x6, x6, x3
	ldp x7, x8, [x0, #112]
	ldp x4, x3, [x0, #144]
	sbcs x7, x7, x4
	sbcs x8, x8, x3
	movz w4, #38, lsl #0
	csel x3, x4, x17, lo
	subs x5, x5, x3
	sbcs x6, x6, x17
	sbcs x7, x7, x17
	sbc x8, x8, x17
	stp x5, x6, [x0, #320]
	stp x7, x8, [x0, #336]
	ldp x3, x4, [x0, #96]
	ldp x7, x8, [x0, #128]
	adds x3, x3, x7
	adcs x4, x4, x8
	ldp x5, x6, [x0, #112]
	ldp x7, x8, [x0, #144]
	adcs x5, x5, x7
	adcs x6, x6, x8
	movz w9, #38, lsl #0
	csel x9, x9, x17, hs
	adds x3, x3, x9
	adcs x4, x4, x17
	adcs x5, x5, x17
	adc x6, x6, x17
	stp x3, x4, [x0, #96]
	stp x5, x6, [x0, #112]
	ldp x2, x3, [x0, #320]
	mul x9, x2, x3
	umulh x10, x2, x3
	ldp x4, x5, [x0, #336]
	mul x11, x2, x5
	umulh x12, x2, x5
	mul x7, x2, x4
	umulh x6, x2, x4
	adds x10, x10, x7
	adcs x11, x11, x6
	mul x7, x3, x4
	umulh x6, x3, x4
	adc x6, x6, x17
	adds x11, x11, x7
	mul x13, x4, x5
	umulh x14, x4, x5
	adcs x12, x12, x6
	mul x7, x3, x5
	umulh x6, x3, x5
	adc x6, x6, x17
	adds x12, x12, x7
	adcs x13, x13, x6
	adc x14, x14, x17
	adds x9, x9, x9
	adcs x10, x10, x10
	adcs x11, x11, x11
	adcs x12, x12, x12
	adcs x13, x13, x13
	adcs x14, x14, x14
	adc x6, x17, x17
	umulh x7, x2, x2
	mul x8, x2, x2
	adds x9, x9, x7
	mul x7, x3, x3
	adcs x10, x10, x7
	umulh x7, x3, x3
	adcs x11, x11, x7
	mul x7, x4, x4
	adcs x12, x12, x7
	umulh x7, x4, x4
	adcs x13, x13, x7
	mul x7, x5, x5
	adcs x14, x14, x7
	umulh x7, x5, x5
	adc x6, x6, x7
	movz w3, #38, lsl #0
	mul x7, x3, x12
	umulh x4, x3, x12
	adds x8, x8, x7
	mul x7, x3, x13
	umulh x13, x3, x13
	adcs x9, x9, x7
	mul x7, x3, x14
	umulh x14, x3, x14
	adcs x10, x10, x7
	mul x7, x3, x6
	umulh x6, x3, x6
	adcs x11, x11, x7
	adc x12, x17, x17
	adds x11, x11, x14
	adc x12, x12, x6
	adds x7, x11, x11
	lsr x11, x7, #1
	adc x2, x12, x12
	movz w3, #19, lsl #0
	mul x7, x3, x2
	adds x8, x8, x7
	adcs x9, x9, x4
	adcs x10, x10, x13
	adc x11, x11, x17
	stp x8, x9, [x0, #320]
	stp x10, x11, [x0, #336]
	ldp x2, x3, [x0, #96]
	mul x9, x2, x3
	umulh x10, x2, x3
	ldp x4, x5, [x0, #112]
	mul x11, x2, x5
	umulh x12, x2, x5
	mul x7, x2, x4
	umulh x6, x2, x4
	adds x10, x10, x7
	adcs x11, x11, x6
	mul x7, x3, x4
	umulh x6, x3, x4
	adc x6, x6, x17
	adds x11, x11, x7
	mul x13, x4, x5
	umulh x14, x4, x5
	adcs x12, x12, x6
	mul x7, x3, x5
	umulh x6, x3, x5
	adc x6, x6, x17
	adds x12, x12, x7
	adcs x13, x13, x6
	adc x14, x14, x17
	adds x9, x9, x9
	adcs x10, x10, x10
	adcs x11, x11, x11
	adcs x12, x12, x12
	adcs x13, x13, x13
	adcs x14, x14, x14
	adc x6, x17, x17
	umulh x7, x2, x2
	mul x8, x2, x2
	adds x9, x9, x7
	mul x7, x3, x3
	adcs x10, x10, x7
	umulh x7, x3, x3
	adcs x11, x11, x7
	mul x7, x4, x4
	adcs x12, x12, x7
	umulh x7, x4, x4
	adcs x13, x13, x7
	mul x7, x5, x5
	adcs x14, x14, x7
	umulh x7, x5, x5
	adc x6, x6, x7
	movz w3, #38, lsl #0
	mul x7, x3, x12
	umulh x4, x3, x12
	adds x8, x8, x7
	mul x7, x3, x13
	umulh x13, x3, x13
	adcs x9, x9, x7
	mul x7, x3, x14
	umulh x14, x3, x14
	adcs x10, x10, x7
	mul x7, x3, x6
	umulh x6, x3, x6
	adcs x11, x11, x7
	adc x12, x17, x17
	adds x11, x11, x14
	adc x12, x12, x6
	adds x7, x11, x11
	lsr x11, x7, #1
	adc x2, x12, x12
	movz w3, #19, lsl #0
	mul x7, x3, x2
	adds x8, x8, x7
	adcs x9, x9, x4
	adcs x10, x10, x13
	adc x11, x11, x17
	stp x8, x9, [x0, #96]
	stp x10, x11, [x0, #112]
	ldp x5, x6, [x0, #96]
	ldp x4, x3, [x0, #320]
	subs x5, x5, x4
	sbcs x6, x6, x3
	ldp x7, x8, [x0, #112]
	ldp x4, x3, [x0, #336]
	sbcs x7, x7, x4
	sbcs x8, x8, x3
	movz w4, #38, lsl #0
	csel x3, x4, x17, lo
	subs x5, x5, x3
	sbcs x6, x6, x17
	sbcs x7, x7, x17
	sbc x8, x8, x17
	stp x5, x6, [x0, #288]
	stp x7, x8, [x0, #304]
	add x20, x1, #0
	movz x1, #56130, lsl #0
	movk x1, #1, lsl #16
	ldp x7, x8, [x0, #288]
	ldp x9, x10, [x0, #304]
	mul x3, x1, x7
	mul x4, x1, x8
	mul x5, x1, x9
	mul x6, x1, x10
	umulh x7, x1, x7
	umulh x8, x1, x8
	umulh x9, x1, x9
	umulh x10, x1, x10
	adds x4, x4, x7
	adcs x5, x5, x8
	adcs x6, x6, x9
	adc x10, x10, x17
	ldp x7, x8, [x0, #320]
	adds x3, x3, x7
	adcs x4, x4, x8
	ldp x7, x8, [x0, #336]
	adcs x5, x5, x7
	adcs x6, x6, x8
	adc x10, x10, x17
	adds x7, x6, x6
	lsr x6, x7, #1
	adc x8, x10, x10
	movz w9, #19, lsl #0
	mul x7, x8, x9
	adds x3, x3, x7
	adcs x4, x4, x17
	adcs x5, x5, x17
	adc x6, x6, x17
	stp x3, x4, [x0, #128]
	stp x5, x6, [x0, #144]
	add x1, x20, #0
	ldp x3, x4, [x0, #96]
	ldp x7, x8, [x0, #320]
	mul x12, x3, x7
	umulh x13, x3, x7
	mul x11, x3, x8
	umulh x14, x3, x8
	adds x13, x13, x11
	ldp x9, x10, [x0, #336]
	mul x11, x3, x9
	umulh x15, x3, x9
	adcs x14, x14, x11
	mul x11, x3, x10
	umulh x16, x3, x10
	adcs x15, x15, x11
	adc x16, x16, x17
	ldp x5, x6, [x0, #112]
	mul x11, x4, x7
	adds x13, x13, x11
	mul x11, x4, x8
	adcs x14, x14, x11
	mul x11, x4, x9
	adcs x15, x15, x11
	mul x11, x4, x10
	adcs x16, x16, x11
	umulh x3, x4, x10
	adc x3, x3, x17
	umulh x11, x4, x7
	adds x14, x14, x11
	umulh x11, x4, x8
	adcs x15, x15, x11
	umulh x11, x4, x9
	adcs x16, x16, x11
	adc x3, x3, x17
	mul x11, x5, x7
	adds x14, x14, x11
	mul x11, x5, x8
	adcs x15, x15, x11
	mul x11, x5, x9
	adcs x16, x16, x11
	mul x11, x5, x10
	adcs x3, x3, x11
	umulh x4, x5, x10
	adc x4, x4, x17
	umulh x11, x5, x7
	adds x15, x15, x11
	umulh x11, x5, x8
	adcs x16, x16, x11
	umulh x11, x5, x9
	adcs x3, x3, x11
	adc x4, x4, x17
	mul x11, x6, x7
	adds x15, x15, x11
	mul x11, x6, x8
	adcs x16, x16, x11
	mul x11, x6, x9
	adcs x3, x3, x11
	mul x11, x6, x10
	adcs x4, x4, x11
	umulh x5, x6, x10
	adc x5, x5, x17
	umulh x11, x6, x7
	adds x16, x16, x11
	umulh x11, x6, x8
	adcs x3, x3, x11
	umulh x11, x6, x9
	adcs x4, x4, x11
	adc x5, x5, x17
	movz w7, #38, lsl #0
	mul x11, x7, x16
	umulh x9, x7, x16
	adds x12, x12, x11
	mul x11, x7, x3
	umulh x3, x7, x3
	adcs x13, x13, x11
	mul x11, x7, x4
	umulh x4, x7, x4
	adcs x14, x14, x11
	mul x11, x7, x5
	umulh x5, x7, x5
	adcs x15, x15, x11
	adc x16, x17, x17
	adds x15, x15, x4
	adc x16, x16, x5
	adds x11, x15, x15
	lsr x15, x11, #1
	adc x8, x16, x16
	movz w7, #19, lsl #0
	mul x11, x7, x8
	adds x12, x12, x11
	adcs x13, x13, x9
	adcs x14, x14, x3
	adc x15, x15, x17
	stp x12, x13, [x0, #96]
	stp x14, x15, [x0, #112]
	ldp x3, x4, [x0, #288]
	ldp x7, x8, [x0, #128]
	mul x12, x3, x7
	umulh x13, x3, x7
	mul x11, x3, x8
	umulh x14, x3, x8
	adds x13, x13, x11
	ldp x9, x10, [x0, #144]
	mul x11, x3, x9
	umulh x15, x3, x9
	adcs x14, x14, x11
	mul x11, x3, x10
	umulh x16, x3, x10
	adcs x15, x15, x11
	adc x16, x16, x17
	ldp x5, x6, [x0, #304]
	mul x11, x4, x7
	adds x13, x13, x11
	mul x11, x4, x8
	adcs x14, x14, x11
	mul x11, x4, x9
	adcs x15, x15, x11
	mul x11, x4, x10
	adcs x16, x16, x11
	umulh x3, x4, x10
	adc x3, x3, x17
	umulh x11, x4, x7
	adds x14, x14, x11
	umulh x11, x4, x8
	adcs x15, x15, x11
	umulh x11, x4, x9
	adcs x16, x16, x11
	adc x3, x3, x17
	mul x11, x5, x7
	adds x14, x14, x11
	mul x11, x5, x8
	adcs x15, x15, x11
	mul x11, x5, x9
	adcs x16, x16, x11
	mul x11, x5, x10
	adcs x3, x3, x11
	umulh x4, x5, x10
	adc x4, x4, x17
	umulh x11, x5, x7
	adds x15, x15, x11
	umulh x11, x5, x8
	adcs x16, x16, x11
	umulh x11, x5, x9
	adcs x3, x3, x11
	adc x4, x4, x17
	mul x11, x6, x7
	adds x15, x15, x11
	mul x11, x6, x8
	adcs x16, x16, x11
	mul x11, x6, x9
	adcs x3, x3, x11
	mul x11, x6, x10
	adcs x4, x4, x11
	umulh x5, x6, x10
	adc x5, x5, x17
	umulh x11, x6, x7
	adds x16, x16, x11
	umulh x11, x6, x8
	adcs x3, x3, x11
	umulh x11, x6, x9
	adcs x4, x4, x11
	adc x5, x5, x17
	movz w7, #38, lsl #0
	mul x11, x7, x16
	umulh x9, x7, x16
	adds x12, x12, x11
	mul x11, x7, x3
	umulh x3, x7, x3
	adcs x13, x13, x11
	mul x11, x7, x4
	umulh x4, x7, x4
	adcs x14, x14, x11
	mul x11, x7, x5
	umulh x5, x7, x5
	adcs x15, x15, x11
	adc x16, x17, x17
	adds x15, x15, x4
	adc x16, x16, x5
	adds x11, x15, x15
	lsr x15, x11, #1
	adc x8, x16, x16
	movz w7, #19, lsl #0
	mul x11, x7, x8
	adds x12, x12, x11
	adcs x13, x13, x9
	adcs x14, x14, x3
	adc x15, x15, x17
	stp x12, x13, [x0, #128]
	stp x14, x15, [x0, #144]
	ldp x5, x6, [x0, #96]
	ldp x4, x3, [x0, #128]
	subs x5, x5, x4
	sbcs x6, x6, x3
	ldp x7, x8, [x0, #112]
	ldp x4, x3, [x0, #144]
	sbcs x7, x7, x4
	sbcs x8, x8, x3
	movz w4, #38, lsl #0
	csel x3, x4, x17, lo
	subs x5, x5, x3
	sbcs x6, x6, x17
	sbcs x7, x7, x17
	sbc x8, x8, x17
	stp x5, x6, [x0, #320]
	stp x7, x8, [x0, #336]
	ldp x3, x4, [x0, #96]
	ldp x7, x8, [x0, #128]
	adds x3, x3, x7
	adcs x4, x4, x8
	ldp x5, x6, [x0, #112]
	ldp x7, x8, [x0, #144]
	adcs x5, x5, x7
	adcs x6, x6, x8
	movz w9, #38, lsl #0
	csel x9, x9, x17, hs
	adds x3, x3, x9
	adcs x4, x4, x17
	adcs x5, x5, x17
	adc x6, x6, x17
	stp x3, x4, [x0, #96]
	stp x5, x6, [x0, #112]
	ldp x2, x3, [x0, #320]
	mul x9, x2, x3
	umulh x10, x2, x3
	ldp x4, x5, [x0, #336]
	mul x11, x2, x5
	umulh x12, x2, x5
	mul x7, x2, x4
	umulh x6, x2, x4
	adds x10, x10, x7
	adcs x11, x11, x6
	mul x7, x3, x4
	umulh x6, x3, x4
	adc x6, x6, x17
	adds x11, x11, x7
	mul x13, x4, x5
	umulh x14, x4, x5
	adcs x12, x12, x6
	mul x7, x3, x5
	umulh x6, x3, x5
	adc x6, x6, x17
	adds x12, x12, x7
	adcs x13, x13, x6
	adc x14, x14, x17
	adds x9, x9, x9
	adcs x10, x10, x10
	adcs x11, x11, x11
	adcs x12, x12, x12
	adcs x13, x13, x13
	adcs x14, x14, x14
	adc x6, x17, x17
	umulh x7, x2, x2
	mul x8, x2, x2
	adds x9, x9, x7
	mul x7, x3, x3
	adcs x10, x10, x7
	umulh x7, x3, x3
	adcs x11, x11, x7
	mul x7, x4, x4
	adcs x12, x12, x7
	umulh x7, x4, x4
	adcs x13, x13, x7
	mul x7, x5, x5
	adcs x14, x14, x7
	umulh x7, x5, x5
	adc x6, x6, x7
	movz w3, #38, lsl #0
	mul x7, x3, x12
	umulh x4, x3, x12
	adds x8, x8, x7
	mul x7, x3, x13
	umulh x13, x3, x13
	adcs x9, x9, x7
	mul x7, x3, x14
	umulh x14, x3, x14
	adcs x10, x10, x7
	mul x7, x3, x6
	umulh x6, x3, x6
	adcs x11, x11, x7
	adc x12, x17, x17
	adds x11, x11, x14
	adc x12, x12, x6
	adds x7, x11, x11
	lsr x11, x7, #1
	adc x2, x12, x12
	movz w3, #19, lsl #0
	mul x7, x3, x2
	adds x8, x8, x7
	adcs x9, x9, x4
	adcs x10, x10, x13
	adc x11, x11, x17
	stp x8, x9, [x0, #320]
	stp x10, x11, [x0, #336]
	ldp x2, x3, [x0, #96]
	mul x9, x2, x3
	umulh x10, x2, x3
	ldp x4, x5, [x0, #112]
	mul x11, x2, x5
	umulh x12, x2, x5
	mul x7, x2, x4
	umulh x6, x2, x4
	adds x10, x10, x7
	adcs x11, x11, x6
	mul x7, x3, x4
	umulh x6, x3, x4
	adc x6, x6, x17
	adds x11, x11, x7
	mul x13, x4, x5
	umulh x14, x4, x5
	adcs x12, x12, x6
	mul x7, x3, x5
	umulh x6, x3, x5
	adc x6, x6, x17
	adds x12, x12, x7
	adcs x13, x13, x6
	adc x14, x14, x17
	adds x9, x9, x9
	adcs x10, x10, x10
	adcs x11, x11, x11
	adcs x12, x12, x12
	adcs x13, x13, x13
	adcs x14, x14, x14
	adc x6, x17, x17
	umulh x7, x2, x2
	mul x8, x2, x2
	adds x9, x9, x7
	mul x7, x3, x3
	adcs x10, x10, x7
	umulh x7, x3, x3
	adcs x11, x11, x7
	mul x7, x4, x4
	adcs x12, x12, x7
	umulh x7, x4, x4
	adcs x13, x13, x7
	mul x7, x5, x5
	adcs x14, x14, x7
	umulh x7, x5, x5
	adc x6, x6, x7
	movz w3, #38, lsl #0
	mul x7, x3, x12
	umulh x4, x3, x12
	adds x8, x8, x7
	mul x7, x3, x13
	umulh x13, x3, x13
	adcs x9, x9, x7
	mul x7, x3, x14
	umulh x14, x3, x14
	adcs x10, x10, x7
	mul x7, x3, x6
	umulh x6, x3, x6
	adcs x11, x11, x7
	adc x12, x17, x17
	adds x11, x11, x14
	adc x12, x12, x6
	adds x7, x11, x11
	lsr x11, x7, #1
	adc x2, x12, x12
	movz w3, #19, lsl #0
	mul x7, x3, x2
	adds x8, x8, x7
	adcs x9, x9, x4
	adcs x10, x10, x13
	adc x11, x11, x17
	stp x8, x9, [x0, #96]
	stp x10, x11, [x0, #112]
	ldp x5, x6, [x0, #96]
	ldp x4, x3, [x0, #320]
	subs x5, x5, x4
	sbcs x6, x6, x3
	ldp x7, x8, [x0, #112]
	ldp x4, x3, [x0, #336]
	sbcs x7, x7, x4
	sbcs x8, x8, x3
	movz w4, #38, lsl #0
	csel x3, x4, x17, lo
	subs x5, x5, x3
	sbcs x6, x6, x17
	sbcs x7, x7, x17
	sbc x8, x8, x17
	stp x5, x6, [x0, #288]
	stp x7, x8, [x0, #304]
	add x20, x1, #0
	movz x1, #56130, lsl #0
	movk x1, #1, lsl #16
	ldp x7, x8, [x0, #288]
	ldp x9, x10, [x0, #304]
	mul x3, x1, x7
	mul x4, x1, x8
	mul x5, x1, x9
	mul x6, x1, x10
	umulh x7, x1, x7
	umulh x8, x1, x8
	umulh x9, x1, x9
	umulh x10, x1, x10
	adds x4, x4, x7
	adcs x5, x5, x8
	adcs x6, x6, x9
	adc x10, x10, x17
	ldp x7, x8, [x0, #320]
	adds x3, x3, x7
	adcs x4, x4, x8
	ldp x7, x8, [x0, #336]
	adcs x5, x5, x7
	adcs x6, x6, x8
	adc x10, x10, x17
	adds x7, x6, x6
	lsr x6, x7, #1
	adc x8, x10, x10
	movz w9, #19, lsl #0
	mul x7, x8, x9
	adds x3, x3, x7
	adcs x4, x4, x17
	adcs x5, x5, x17
	adc x6, x6, x17
	stp x3, x4, [x0, #128]
	stp x5, x6, [x0, #144]
	add x1, x20, #0
	ldp x3, x4, [x0, #96]
	ldp x7, x8, [x0, #320]
	mul x12, x3, x7
	umulh x13, x3, x7
	mul x11, x3, x8
	umulh x14, x3, x8
	adds x13, x13, x11
	ldp x9, x10, [x0, #336]
	mul x11, x3, x9
	umulh x15, x3, x9
	adcs x14, x14, x11
	mul x11, x3, x10
	umulh x16, x3, x10
	adcs x15, x15, x11
	adc x16, x16, x17
	ldp x5, x6, [x0, #112]
	mul x11, x4, x7
	adds x13, x13, x11
	mul x11, x4, x8
	adcs x14, x14, x11
	mul x11, x4, x9
	adcs x15, x15, x11
	mul x11, x4, x10
	adcs x16, x16, x11
	umulh x3, x4, x10
	adc x3, x3, x17
	umulh x11, x4, x7
	adds x14, x14, x11
	umulh x11, x4, x8
	adcs x15, x15, x11
	umulh x11, x4, x9
	adcs x16, x16, x11
	adc x3, x3, x17
	mul x11, x5, x7
	adds x14, x14, x11
	mul x11, x5, x8
	adcs x15, x15, x11
	mul x11, x5, x9
	adcs x16, x16, x11
	mul x11, x5, x10
	adcs x3, x3, x11
	umulh x4, x5, x10
	adc x4, x4, x17
	umulh x11, x5, x7
	adds x15, x15, x11
	umulh x11, x5, x8
	adcs x16, x16, x11
	umulh x11, x5, x9
	adcs x3, x3, x11
	adc x4, x4, x17
	mul x11, x6, x7
	adds x15, x15, x11
	mul x11, x6, x8
	adcs x16, x16, x11
	mul x11, x6, x9
	adcs x3, x3, x11
	mul x11, x6, x10
	adcs x4, x4, x11
	umulh x5, x6, x10
	adc x5, x5, x17
	umulh x11, x6, x7
	adds x16, x16, x11
	umulh x11, x6, x8
	adcs x3, x3, x11
	umulh x11, x6, x9
	adcs x4, x4, x11
	adc x5, x5, x17
	movz w7, #38, lsl #0
	mul x11, x7, x16
	umulh x9, x7, x16
	adds x12, x12, x11
	mul x11, x7, x3
	umulh x3, x7, x3
	adcs x13, x13, x11
	mul x11, x7, x4
	umulh x4, x7, x4
	adcs x14, x14, x11
	mul x11, x7, x5
	umulh x5, x7, x5
	adcs x15, x15, x11
	adc x16, x17, x17
	adds x15, x15, x4
	adc x16, x16, x5
	adds x11, x15, x15
	lsr x15, x11, #1
	adc x8, x16, x16
	movz w7, #19, lsl #0
	mul x11, x7, x8
	adds x12, x12, x11
	adcs x13, x13, x9
	adcs x14, x14, x3
	adc x15, x15, x17
	stp x12, x13, [x0, #96]
	stp x14, x15, [x0, #112]
	ldp x3, x4, [x0, #288]
	ldp x7, x8, [x0, #128]
	mul x12, x3, x7
	umulh x13, x3, x7
	mul x11, x3, x8
	umulh x14, x3, x8
	adds x13, x13, x11
	ldp x9, x10, [x0, #144]
	mul x11, x3, x9
	umulh x15, x3, x9
	adcs x14, x14, x11
	mul x11, x3, x10
	umulh x16, x3, x10
	adcs x15, x15, x11
	adc x16, x16, x17
	ldp x5, x6, [x0, #304]
	mul x11, x4, x7
	adds x13, x13, x11
	mul x11, x4, x8
	adcs x14, x14, x11
	mul x11, x4, x9
	adcs x15, x15, x11
	mul x11, x4, x10
	adcs x16, x16, x11
	umulh x3, x4, x10
	adc x3, x3, x17
	umulh x11, x4, x7
	adds x14, x14, x11
	umulh x11, x4, x8
	adcs x15, x15, x11
	umulh x11, x4, x9
	adcs x16, x16, x11
	adc x3, x3, x17
	mul x11, x5, x7
	adds x14, x14, x11
	mul x11, x5, x8
	adcs x15, x15, x11
	mul x11, x5, x9
	adcs x16, x16, x11
	mul x11, x5, x10
	adcs x3, x3, x11
	umulh x4, x5, x10
	adc x4, x4, x17
	umulh x11, x5, x7
	adds x15, x15, x11
	umulh x11, x5, x8
	adcs x16, x16, x11
	umulh x11, x5, x9
	adcs x3, x3, x11
	adc x4, x4, x17
	mul x11, x6, x7
	adds x15, x15, x11
	mul x11, x6, x8
	adcs x16, x16, x11
	mul x11, x6, x9
	adcs x3, x3, x11
	mul x11, x6, x10
	adcs x4, x4, x11
	umulh x5, x6, x10
	adc x5, x5, x17
	umulh x11, x6, x7
	adds x16, x16, x11
	umulh x11, x6, x8
	adcs x3, x3, x11
	umulh x11, x6, x9
	adcs x4, x4, x11
	adc x5, x5, x17
	movz w7, #38, lsl #0
	mul x11, x7, x16
	umulh x9, x7, x16
	adds x12, x12, x11
	mul x11, x7, x3
	umulh x3, x7, x3
	adcs x13, x13, x11
	mul x11, x7, x4
	umulh x4, x7, x4
	adcs x14, x14, x11
	mul x11, x7, x5
	umulh x5, x7, x5
	adcs x15, x15, x11
	adc x16, x17, x17
	adds x15, x15, x4
	adc x16, x16, x5
	adds x11, x15, x15
	lsr x15, x11, #1
	adc x8, x16, x16
	movz w7, #19, lsl #0
	mul x11, x7, x8
	adds x12, x12, x11
	adcs x13, x13, x9
	adcs x14, x14, x3
	adc x15, x15, x17
	stp x12, x13, [x0, #128]
	stp x14, x15, [x0, #144]
	ldp x5, x6, [x0, #96]
	ldp x4, x3, [x0, #128]
	subs x5, x5, x4
	sbcs x6, x6, x3
	ldp x7, x8, [x0, #112]
	ldp x4, x3, [x0, #144]
	sbcs x7, x7, x4
	sbcs x8, x8, x3
	movz w4, #38, lsl #0
	csel x3, x4, x17, lo
	subs x5, x5, x3
	sbcs x6, x6, x17
	sbcs x7, x7, x17
	sbc x8, x8, x17
	stp x5, x6, [x0, #320]
	stp x7, x8, [x0, #336]
	ldp x3, x4, [x0, #96]
	ldp x7, x8, [x0, #128]
	adds x3, x3, x7
	adcs x4, x4, x8
	ldp x5, x6, [x0, #112]
	ldp x7, x8, [x0, #144]
	adcs x5, x5, x7
	adcs x6, x6, x8
	movz w9, #38, lsl #0
	csel x9, x9, x17, hs
	adds x3, x3, x9
	adcs x4, x4, x17
	adcs x5, x5, x17
	adc x6, x6, x17
	stp x3, x4, [x0, #96]
	stp x5, x6, [x0, #112]
	ldp x2, x3, [x0, #320]
	mul x9, x2, x3
	umulh x10, x2, x3
	ldp x4, x5, [x0, #336]
	mul x11, x2, x5
	umulh x12, x2, x5
	mul x7, x2, x4
	umulh x6, x2, x4
	adds x10, x10, x7
	adcs x11, x11, x6
	mul x7, x3, x4
	umulh x6, x3, x4
	adc x6, x6, x17
	adds x11, x11, x7
	mul x13, x4, x5
	umulh x14, x4, x5
	adcs x12, x12, x6
	mul x7, x3, x5
	umulh x6, x3, x5
	adc x6, x6, x17
	adds x12, x12, x7
	adcs x13, x13, x6
	adc x14, x14, x17
	adds x9, x9, x9
	adcs x10, x10, x10
	adcs x11, x11, x11
	adcs x12, x12, x12
	adcs x13, x13, x13
	adcs x14, x14, x14
	adc x6, x17, x17
	umulh x7, x2, x2
	mul x8, x2, x2
	adds x9, x9, x7
	mul x7, x3, x3
	adcs x10, x10, x7
	umulh x7, x3, x3
	adcs x11, x11, x7
	mul x7, x4, x4
	adcs x12, x12, x7
	umulh x7, x4, x4
	adcs x13, x13, x7
	mul x7, x5, x5
	adcs x14, x14, x7
	umulh x7, x5, x5
	adc x6, x6, x7
	movz w3, #38, lsl #0
	mul x7, x3, x12
	umulh x4, x3, x12
	adds x8, x8, x7
	mul x7, x3, x13
	umulh x13, x3, x13
	adcs x9, x9, x7
	mul x7, x3, x14
	umulh x14, x3, x14
	adcs x10, x10, x7
	mul x7, x3, x6
	umulh x6, x3, x6
	adcs x11, x11, x7
	adc x12, x17, x17
	adds x11, x11, x14
	adc x12, x12, x6
	adds x7, x11, x11
	lsr x11, x7, #1
	adc x2, x12, x12
	movz w3, #19, lsl #0
	mul x7, x3, x2
	adds x8, x8, x7
	adcs x9, x9, x4
	adcs x10, x10, x13
	adc x11, x11, x17
	stp x8, x9, [x0, #320]
	stp x10, x11, [x0, #336]
	ldp x2, x3, [x0, #96]
	mul x9, x2, x3
	umulh x10, x2, x3
	ldp x4, x5, [x0, #112]
	mul x11, x2, x5
	umulh x12, x2, x5
	mul x7, x2, x4
	umulh x6, x2, x4
	adds x10, x10, x7
	adcs x11, x11, x6
	mul x7, x3, x4
	umulh x6, x3, x4
	adc x6, x6, x17
	adds x11, x11, x7
	mul x13, x4, x5
	umulh x14, x4, x5
	adcs x12, x12, x6
	mul x7, x3, x5
	umulh x6, x3, x5
	adc x6, x6, x17
	adds x12, x12, x7
	adcs x13, x13, x6
	adc x14, x14, x17
	adds x9, x9, x9
	adcs x10, x10, x10
	adcs x11, x11, x11
	adcs x12, x12, x12
	adcs x13, x13, x13
	adcs x14, x14, x14
	adc x6, x17, x17
	umulh x7, x2, x2
	mul x8, x2, x2
	adds x9, x9, x7
	mul x7, x3, x3
	adcs x10, x10, x7
	umulh x7, x3, x3
	adcs x11, x11, x7
	mul x7, x4, x4
	adcs x12, x12, x7
	umulh x7, x4, x4
	adcs x13, x13, x7
	mul x7, x5, x5
	adcs x14, x14, x7
	umulh x7, x5, x5
	adc x6, x6, x7
	movz w3, #38, lsl #0
	mul x7, x3, x12
	umulh x4, x3, x12
	adds x8, x8, x7
	mul x7, x3, x13
	umulh x13, x3, x13
	adcs x9, x9, x7
	mul x7, x3, x14
	umulh x14, x3, x14
	adcs x10, x10, x7
	mul x7, x3, x6
	umulh x6, x3, x6
	adcs x11, x11, x7
	adc x12, x17, x17
	adds x11, x11, x14
	adc x12, x12, x6
	adds x7, x11, x11
	lsr x11, x7, #1
	adc x2, x12, x12
	movz w3, #19, lsl #0
	mul x7, x3, x2
	adds x8, x8, x7
	adcs x9, x9, x4
	adcs x10, x10, x13
	adc x11, x11, x17
	stp x8, x9, [x0, #96]
	stp x10, x11, [x0, #112]
	ldp x5, x6, [x0, #96]
	ldp x4, x3, [x0, #320]
	subs x5, x5, x4
	sbcs x6, x6, x3
	ldp x7, x8, [x0, #112]
	ldp x4, x3, [x0, #336]
	sbcs x7, x7, x4
	sbcs x8, x8, x3
	movz w4, #38, lsl #0
	csel x3, x4, x17, lo
	subs x5, x5, x3
	sbcs x6, x6, x17
	sbcs x7, x7, x17
	sbc x8, x8, x17
	stp x5, x6, [x0, #288]
	stp x7, x8, [x0, #304]
	add x20, x1, #0
	movz x1, #56130, lsl #0
	movk x1, #1, lsl #16
	ldp x7, x8, [x0, #288]
	ldp x9, x10, [x0, #304]
	mul x3, x1, x7
	mul x4, x1, x8
	mul x5, x1, x9
	mul x6, x1, x10
	umulh x7, x1, x7
	umulh x8, x1, x8
	umulh x9, x1, x9
	umulh x10, x1, x10
	adds x4, x4, x7
	adcs x5, x5, x8
	adcs x6, x6, x9
	adc x10, x10, x17
	ldp x7, x8, [x0, #320]
	adds x3, x3, x7
	adcs x4, x4, x8
	ldp x7, x8, [x0, #336]
	adcs x5, x5, x7
	adcs x6, x6, x8
	adc x10, x10, x17
	adds x7, x6, x6
	lsr x6, x7, #1
	adc x8, x10, x10
	movz w9, #19, lsl #0
	mul x7, x8, x9
	adds x3, x3, x7
	adcs x4, x4, x17
	adcs x5, x5, x17
	adc x6, x6, x17
	stp x3, x4, [x0, #128]
	stp x5, x6, [x0, #144]
	add x1, x20, #0
	ldp x3, x4, [x0, #96]
	ldp x7, x8, [x0, #320]
	mul x12, x3, x7
	umulh x13, x3, x7
	mul x11, x3, x8
	umulh x14, x3, x8
	adds x13, x13, x11
	ldp x9, x10, [x0, #336]
	mul x11, x3, x9
	umulh x15, x3, x9
	adcs x14, x14, x11
	mul x11, x3, x10
	umulh x16, x3, x10
	adcs x15, x15, x11
	adc x16, x16, x17
	ldp x5, x6, [x0, #112]
	mul x11, x4, x7
	adds x13, x13, x11
	mul x11, x4, x8
	adcs x14, x14, x11
	mul x11, x4, x9
	adcs x15, x15, x11
	mul x11, x4, x10
	adcs x16, x16, x11
	umulh x3, x4, x10
	adc x3, x3, x17
	umulh x11, x4, x7
	adds x14, x14, x11
	umulh x11, x4, x8
	adcs x15, x15, x11
	umulh x11, x4, x9
	adcs x16, x16, x11
	adc x3, x3, x17
	mul x11, x5, x7
	adds x14, x14, x11
	mul x11, x5, x8
	adcs x15, x15, x11
	mul x11, x5, x9
	adcs x16, x16, x11
	mul x11, x5, x10
	adcs x3, x3, x11
	umulh x4, x5, x10
	adc x4, x4, x17
	umulh x11, x5, x7
	adds x15, x15, x11
	umulh x11, x5, x8
	adcs x16, x16, x11
	umulh x11, x5, x9
	adcs x3, x3, x11
	adc x4, x4, x17
	mul x11, x6, x7
	adds x15, x15, x11
	mul x11, x6, x8
	adcs x16, x16, x11
	mul x11, x6, x9
	adcs x3, x3, x11
	mul x11, x6, x10
	adcs x4, x4, x11
	umulh x5, x6, x10
	adc x5, x5, x17
	umulh x11, x6, x7
	adds x16, x16, x11
	umulh x11, x6, x8
	adcs x3, x3, x11
	umulh x11, x6, x9
	adcs x4, x4, x11
	adc x5, x5, x17
	movz w7, #38, lsl #0
	mul x11, x7, x16
	umulh x9, x7, x16
	adds x12, x12, x11
	mul x11, x7, x3
	umulh x3, x7, x3
	adcs x13, x13, x11
	mul x11, x7, x4
	umulh x4, x7, x4
	adcs x14, x14, x11
	mul x11, x7, x5
	umulh x5, x7, x5
	adcs x15, x15, x11
	adc x16, x17, x17
	adds x15, x15, x4
	adc x16, x16, x5
	adds x11, x15, x15
	lsr x15, x11, #1
	adc x8, x16, x16
	movz w7, #19, lsl #0
	mul x11, x7, x8
	adds x12, x12, x11
	adcs x13, x13, x9
	adcs x14, x14, x3
	adc x15, x15, x17
	stp x12, x13, [x0, #96]
	stp x14, x15, [x0, #112]
	ldp x3, x4, [x0, #288]
	ldp x7, x8, [x0, #128]
	mul x12, x3, x7
	umulh x13, x3, x7
	mul x11, x3, x8
	umulh x14, x3, x8
	adds x13, x13, x11
	ldp x9, x10, [x0, #144]
	mul x11, x3, x9
	umulh x15, x3, x9
	adcs x14, x14, x11
	mul x11, x3, x10
	umulh x16, x3, x10
	adcs x15, x15, x11
	adc x16, x16, x17
	ldp x5, x6, [x0, #304]
	mul x11, x4, x7
	adds x13, x13, x11
	mul x11, x4, x8
	adcs x14, x14, x11
	mul x11, x4, x9
	adcs x15, x15, x11
	mul x11, x4, x10
	adcs x16, x16, x11
	umulh x3, x4, x10
	adc x3, x3, x17
	umulh x11, x4, x7
	adds x14, x14, x11
	umulh x11, x4, x8
	adcs x15, x15, x11
	umulh x11, x4, x9
	adcs x16, x16, x11
	adc x3, x3, x17
	mul x11, x5, x7
	adds x14, x14, x11
	mul x11, x5, x8
	adcs x15, x15, x11
	mul x11, x5, x9
	adcs x16, x16, x11
	mul x11, x5, x10
	adcs x3, x3, x11
	umulh x4, x5, x10
	adc x4, x4, x17
	umulh x11, x5, x7
	adds x15, x15, x11
	umulh x11, x5, x8
	adcs x16, x16, x11
	umulh x11, x5, x9
	adcs x3, x3, x11
	adc x4, x4, x17
	mul x11, x6, x7
	adds x15, x15, x11
	mul x11, x6, x8
	adcs x16, x16, x11
	mul x11, x6, x9
	adcs x3, x3, x11
	mul x11, x6, x10
	adcs x4, x4, x11
	umulh x5, x6, x10
	adc x5, x5, x17
	umulh x11, x6, x7
	adds x16, x16, x11
	umulh x11, x6, x8
	adcs x3, x3, x11
	umulh x11, x6, x9
	adcs x4, x4, x11
	adc x5, x5, x17
	movz w7, #38, lsl #0
	mul x11, x7, x16
	umulh x9, x7, x16
	adds x12, x12, x11
	mul x11, x7, x3
	umulh x3, x7, x3
	adcs x13, x13, x11
	mul x11, x7, x4
	umulh x4, x7, x4
	adcs x14, x14, x11
	mul x11, x7, x5
	umulh x5, x7, x5
	adcs x15, x15, x11
	adc x16, x17, x17
	adds x15, x15, x4
	adc x16, x16, x5
	adds x11, x15, x15
	lsr x15, x11, #1
	adc x8, x16, x16
	movz w7, #19, lsl #0
	mul x11, x7, x8
	adds x12, x12, x11
	adcs x13, x13, x9
	adcs x14, x14, x3
	adc x15, x15, x17
	stp x12, x13, [x0, #128]
	stp x14, x15, [x0, #144]
	add x19, x1, #0
	movz x12, #0, lsl #0
	movz x6, #19, lsl #0
	movz x7, #65535, lsl #0
	movk x7, #65535, lsl #16
	movk x7, #65535, lsl #32
	movk x7, #32767, lsl #48
	ldr x2, [x0, #128]
	ldr x3, [x0, #136]
	ldr x4, [x0, #144]
	ldr x5, [x0, #152]
	lsr x8, x5, #63
	and x5, x5, x7
	mul x8, x8, x6
	adds x2, x2, x8
	adcs x3, x3, x12
	adcs x4, x4, x12
	adc x5, x5, x12
	adds x8, x2, x6
	adcs x9, x3, x12
	adcs x10, x4, x12
	adc x11, x5, x12
	lsr x13, x11, #63
	and x11, x11, x7
	sub x13, x12, x13
	eor x8, x8, x2
	and x8, x8, x13
	eor x2, x2, x8
	eor x9, x9, x3
	and x9, x9, x13
	eor x3, x3, x9
	eor x10, x10, x4
	and x10, x10, x13
	eor x4, x4, x10
	eor x11, x11, x5
	and x11, x11, x13
	eor x5, x5, x11
	str x2, [x0, #224]
	str x3, [x0, #232]
	str x4, [x0, #240]
	str x5, [x0, #248]
	movz x2, #65517, lsl #0
	movk x2, #65535, lsl #16
	movk x2, #65535, lsl #32
	movk x2, #65535, lsl #48
	str x2, [x0, #192]
	movz x2, #65535, lsl #0
	movk x2, #65535, lsl #16
	movk x2, #65535, lsl #32
	movk x2, #65535, lsl #48
	str x2, [x0, #200]
	movz x2, #65535, lsl #0
	movk x2, #65535, lsl #16
	movk x2, #65535, lsl #32
	movk x2, #65535, lsl #48
	str x2, [x0, #208]
	movz x2, #65535, lsl #0
	movk x2, #65535, lsl #16
	movk x2, #65535, lsl #32
	movk x2, #32767, lsl #48
	str x2, [x0, #216]
	str x12, [x0, #256]
	str x12, [x0, #264]
	str x12, [x0, #272]
	str x12, [x0, #280]
	movz x2, #8345, lsl #0
	movk x2, #29954, lsl #16
	movk x2, #40483, lsl #32
	movk x2, #41209, lsl #48
	str x2, [x0, #288]
	movz x2, #9621, lsl #0
	movk x2, #7443, lsl #16
	movk x2, #36671, lsl #32
	movk x2, #43206, lsl #48
	str x2, [x0, #296]
	movz x2, #21058, lsl #0
	movk x2, #1452, lsl #16
	movk x2, #35128, lsl #32
	movk x2, #27756, lsl #48
	str x2, [x0, #304]
	movz x2, #1557, lsl #0
	movk x2, #16759, lsl #16
	movk x2, #2226, lsl #32
	movk x2, #10085, lsl #48
	str x2, [x0, #312]
	movz x1, #1, lsl #0
	str x1, [x0, #480]
	movz x20, #10, lsl #0
21:
	ldr x1, [x0, #480]
	ldr x2, [x0, #192]
	ldr x3, [x0, #224]
	movz x13, #0, lsl #0
	sub x1, x13, x1
	sub x1, x1, #1
	movz x13, #32767, lsl #0
	and x8, x2, x13
	and x9, x3, x13
	movz x16, #32768, lsl #16
	add x8, x8, x16
	movz x16, #32768, lsl #32
	add x9, x9, x16
	movz x12, #1, lsl #0
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x1, #0, #0, ne
	csel x9, x11, x9, mi
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x1, #0, #0, ne
	csel x9, x11, x9, mi
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x1, #0, #0, ne
	csel x9, x11, x9, mi
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x1, #0, #0, ne
	csel x9, x11, x9, mi
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x1, #0, #0, ne
	csel x9, x11, x9, mi
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x1, #0, #0, ne
	csel x9, x11, x9, mi
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x1, #0, #0, ne
	csel x9, x11, x9, mi
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	movz x13, #16384, lsl #16
	movk x13, #8192, lsl #32
	movk x13, #8192, lsl #48
	movz x17, #16384, lsl #0
	add x8, x8, x13
	add x10, x10, x13
	lsr x11, x8, #47
	sub x11, x11, x17
	lsl x8, x8, #17
	lsr x8, x8, #48
	sub x8, x8, x17
	lsr x9, x10, #47
	sub x9, x9, x17
	lsl x10, x10, #17
	lsr x10, x10, #48
	sub x10, x10, x17
	mul x13, x2, x8
	madd x13, x3, x11, x13
	mul x16, x2, x10
	madd x16, x3, x9, x16
	lsr x2, x13, #15
	lsr x3, x16, #15
	orr x4, x8, x8
	orr x5, x11, x11
	orr x6, x10, x10
	orr x7, x9, x9
	movz x13, #32767, lsl #0
	and x8, x2, x13
	and x9, x3, x13
	movz x16, #32768, lsl #16
	add x8, x8, x16
	movz x16, #32768, lsl #32
	add x9, x9, x16
	movz x12, #1, lsl #0
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x1, #0, #0, ne
	csel x9, x11, x9, mi
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x1, #0, #0, ne
	csel x9, x11, x9, mi
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x1, #0, #0, ne
	csel x9, x11, x9, mi
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x1, #0, #0, ne
	csel x9, x11, x9, mi
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x1, #0, #0, ne
	csel x9, x11, x9, mi
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x1, #0, #0, ne
	csel x9, x11, x9, mi
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x1, #0, #0, ne
	csel x9, x11, x9, mi
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	movz x13, #16384, lsl #16
	movk x13, #8192, lsl #32
	movk x13, #8192, lsl #48
	movz x17, #16384, lsl #0
	add x8, x8, x13
	add x10, x10, x13
	lsr x11, x8, #47
	sub x11, x11, x17
	lsl x8, x8, #17
	lsr x8, x8, #48
	sub x8, x8, x17
	lsr x9, x10, #47
	sub x9, x9, x17
	lsl x10, x10, #17
	lsr x10, x10, #48
	sub x10, x10, x17
	mul x13, x2, x8
	madd x13, x3, x11, x13
	mul x16, x2, x10
	madd x16, x3, x9, x16
	lsr x2, x13, #15
	lsr x3, x16, #15
	mul x13, x8, x4
	madd x13, x11, x6, x13
	mul x16, x10, x4
	madd x6, x9, x6, x16
	mul x17, x8, x5
	madd x17, x11, x7, x17
	mul x16, x10, x5
	madd x7, x9, x7, x16
	orr x4, x13, x13
	orr x5, x17, x17
	movz x13, #32767, lsl #0
	and x8, x2, x13
	and x9, x3, x13
	movz x16, #32768, lsl #16
	add x8, x8, x16
	movz x16, #32768, lsl #32
	add x9, x9, x16
	movz x12, #1, lsl #0
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x1, #0, #0, ne
	csel x9, x11, x9, mi
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x1, #0, #0, ne
	csel x9, x11, x9, mi
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x1, #0, #0, ne
	csel x9, x11, x9, mi
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x1, #0, #0, ne
	csel x9, x11, x9, mi
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x1, #0, #0, ne
	csel x9, x11, x9, mi
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x1, #0, #0, ne
	csel x9, x11, x9, mi
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x1, #0, #0, ne
	csel x9, x11, x9, mi
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	movz x13, #16384, lsl #16
	movk x13, #8192, lsl #32
	movk x13, #8192, lsl #48
	movz x17, #16384, lsl #0
	add x8, x8, x13
	add x10, x10, x13
	lsr x11, x8, #47
	sub x11, x11, x17
	lsl x8, x8, #17
	lsr x8, x8, #48
	sub x8, x8, x17
	lsr x9, x10, #47
	sub x9, x9, x17
	lsl x10, x10, #17
	lsr x10, x10, #48
	sub x10, x10, x17
	mul x13, x2, x8
	madd x13, x3, x11, x13
	mul x16, x2, x10
	madd x16, x3, x9, x16
	lsr x2, x13, #15
	lsr x3, x16, #15
	mul x13, x8, x4
	madd x13, x11, x6, x13
	mul x16, x10, x4
	madd x6, x9, x6, x16
	mul x17, x8, x5
	madd x17, x11, x7, x17
	mul x16, x10, x5
	madd x7, x9, x7, x16
	orr x4, x13, x13
	orr x5, x17, x17
	movz x13, #32767, lsl #0
	and x8, x2, x13
	and x9, x3, x13
	movz x16, #32768, lsl #16
	add x8, x8, x16
	movz x16, #32768, lsl #32
	add x9, x9, x16
	movz x12, #1, lsl #0
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x1, #0, #0, ne
	csel x9, x11, x9, mi
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x1, #0, #0, ne
	csel x9, x11, x9, mi
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x1, #0, #0, ne
	csel x9, x11, x9, mi
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x1, #0, #0, ne
	csel x9, x11, x9, mi
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x1, #0, #0, ne
	csel x9, x11, x9, mi
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x1, #0, #0, ne
	csel x9, x11, x9, mi
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x1, #0, #0, ne
	csel x9, x11, x9, mi
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	movz x13, #16384, lsl #16
	movk x13, #8192, lsl #32
	movk x13, #8192, lsl #48
	movz x17, #16384, lsl #0
	add x8, x8, x13
	add x9, x9, x13
	lsr x11, x8, #47
	sub x11, x11, x17
	lsl x8, x8, #17
	lsr x8, x8, #48
	sub x8, x8, x17
	lsr x10, x9, #47
	sub x10, x10, x17
	lsl x9, x9, #17
	lsr x9, x9, #48
	sub x9, x9, x17
	mul x13, x8, x4
	madd x13, x11, x6, x13
	mul x16, x9, x4
	madd x6, x10, x6, x16
	mul x17, x8, x5
	madd x17, x11, x7, x17
	mul x16, x9, x5
	madd x7, x10, x7, x16
	orr x4, x13, x13
	orr x5, x17, x17
	movz x13, #0, lsl #0
	sub x1, x13, x1
	sub x1, x1, #1
	str x1, [x0, #480]
	movz x12, #0, lsl #0
	lsr x14, x4, #63
	sub x14, x12, x14
	eor x4, x4, x14
	sub x4, x4, x14
	lsr x15, x5, #63
	sub x15, x12, x15
	eor x5, x5, x15
	sub x5, x5, x15
	lsr x16, x6, #63
	sub x16, x12, x16
	eor x6, x6, x16
	sub x6, x6, x16
	lsr x17, x7, #63
	sub x17, x12, x17
	eor x7, x7, x17
	sub x7, x7, x17
	and x8, x4, x14
	and x9, x5, x15
	add x13, x8, x9
	and x8, x6, x16
	and x9, x7, x17
	add x11, x8, x9
	ldr x8, [x0, #192]
	eor x8, x8, x14
	mul x9, x8, x4
	umulh x10, x8, x4
	adds x1, x13, x9
	adc x2, x12, x10
	ldr x8, [x0, #224]
	eor x8, x8, x15
	mul x9, x8, x5
	umulh x10, x8, x5
	adds x1, x1, x9
	adc x2, x2, x10
	str x1, [x0, #320]
	ldr x8, [x0, #200]
	eor x8, x8, x14
	mul x9, x8, x4
	umulh x10, x8, x4
	adds x1, x2, x9
	adc x2, x12, x10
	ldr x8, [x0, #232]
	eor x8, x8, x15
	mul x9, x8, x5
	umulh x10, x8, x5
	adds x1, x1, x9
	adc x2, x2, x10
	str x1, [x0, #328]
	ldr x8, [x0, #208]
	eor x8, x8, x14
	mul x9, x8, x4
	umulh x10, x8, x4
	adds x1, x2, x9
	adc x2, x12, x10
	ldr x8, [x0, #240]
	eor x8, x8, x15
	mul x9, x8, x5
	umulh x10, x8, x5
	adds x1, x1, x9
	adc x2, x2, x10
	str x1, [x0, #336]
	ldr x8, [x0, #216]
	eor x8, x8, x14
	lsr x3, x8, #63
	sub x3, x12, x3
	and x3, x3, x4
	sub x3, x12, x3
	mul x9, x8, x4
	umulh x10, x8, x4
	adds x1, x2, x9
	adc x3, x3, x10
	ldr x8, [x0, #248]
	eor x8, x8, x15
	lsr x2, x8, #63
	sub x2, x12, x2
	and x2, x2, x5
	sub x2, x12, x2
	add x3, x3, x2
	mul x9, x8, x5
	umulh x10, x8, x5
	adds x1, x1, x9
	adc x3, x3, x10
	str x1, [x0, #344]
	str x3, [x0, #352]
	ldr x8, [x0, #192]
	eor x8, x8, x16
	mul x9, x8, x6
	umulh x10, x8, x6
	adds x1, x11, x9
	adc x2, x12, x10
	ldr x8, [x0, #224]
	eor x8, x8, x17
	mul x9, x8, x7
	umulh x10, x8, x7
	adds x1, x1, x9
	adc x2, x2, x10
	str x1, [x0, #360]
	ldr x8, [x0, #200]
	eor x8, x8, x16
	mul x9, x8, x6
	umulh x10, x8, x6
	adds x1, x2, x9
	adc x2, x12, x10
	ldr x8, [x0, #232]
	eor x8, x8, x17
	mul x9, x8, x7
	umulh x10, x8, x7
	adds x1, x1, x9
	adc x2, x2, x10
	str x1, [x0, #368]
	ldr x8, [x0, #208]
	eor x8, x8, x16
	mul x9, x8, x6
	umulh x10, x8, x6
	adds x1, x2, x9
	adc x2, x12, x10
	ldr x8, [x0, #240]
	eor x8, x8, x17
	mul x9, x8, x7
	umulh x10, x8, x7
	adds x1, x1, x9
	adc x2, x2, x10
	str x1, [x0, #376]
	ldr x8, [x0, #216]
	eor x8, x8, x16
	lsr x3, x8, #63
	sub x3, x12, x3
	and x3, x3, x6
	sub x3, x12, x3
	mul x9, x8, x6
	umulh x10, x8, x6
	adds x1, x2, x9
	adc x3, x3, x10
	ldr x8, [x0, #248]
	eor x8, x8, x17
	lsr x2, x8, #63
	sub x2, x12, x2
	and x2, x2, x7
	sub x2, x12, x2
	add x3, x3, x2
	mul x9, x8, x7
	umulh x10, x8, x7
	adds x1, x1, x9
	adc x3, x3, x10
	str x1, [x0, #384]
	str x3, [x0, #392]
	ldr x8, [x0, #256]
	eor x8, x8, x14
	mul x9, x8, x4
	umulh x10, x8, x4
	adds x1, x13, x9
	adc x2, x12, x10
	ldr x8, [x0, #288]
	eor x8, x8, x15
	mul x9, x8, x5
	umulh x10, x8, x5
	adds x1, x1, x9
	adc x2, x2, x10
	str x1, [x0, #400]
	ldr x8, [x0, #264]
	eor x8, x8, x14
	mul x9, x8, x4
	umulh x10, x8, x4
	adds x1, x2, x9
	adc x2, x12, x10
	ldr x8, [x0, #296]
	eor x8, x8, x15
	mul x9, x8, x5
	umulh x10, x8, x5
	adds x1, x1, x9
	adc x2, x2, x10
	str x1, [x0, #408]
	ldr x8, [x0, #272]
	eor x8, x8, x14
	mul x9, x8, x4
	umulh x10, x8, x4
	adds x1, x2, x9
	adc x2, x12, x10
	ldr x8, [x0, #304]
	eor x8, x8, x15
	mul x9, x8, x5
	umulh x10, x8, x5
	adds x1, x1, x9
	adc x2, x2, x10
	str x1, [x0, #416]
	ldr x8, [x0, #280]
	eor x8, x8, x14
	and x3, x14, x4
	sub x3, x12, x3
	mul x9, x8, x4
	umulh x10, x8, x4
	adds x1, x2, x9
	adc x3, x3, x10
	ldr x8, [x0, #312]
	eor x8, x8, x15
	and x2, x15, x5
	sub x2, x12, x2
	add x3, x3, x2
	mul x9, x8, x5
	umulh x10, x8, x5
	adds x1, x1, x9
	adc x3, x3, x10
	str x1, [x0, #424]
	str x3, [x0, #432]
	ldr x8, [x0, #256]
	eor x8, x8, x16
	mul x9, x8, x6
	umulh x10, x8, x6
	adds x1, x11, x9
	adc x2, x12, x10
	ldr x8, [x0, #288]
	eor x8, x8, x17
	mul x9, x8, x7
	umulh x10, x8, x7
	adds x1, x1, x9
	adc x2, x2, x10
	str x1, [x0, #440]
	ldr x8, [x0, #264]
	eor x8, x8, x16
	mul x9, x8, x6
	umulh x10, x8, x6
	adds x1, x2, x9
	adc x2, x12, x10
	ldr x8, [x0, #296]
	eor x8, x8, x17
	mul x9, x8, x7
	umulh x10, x8, x7
	adds x1, x1, x9
	adc x2, x2, x10
	str x1, [x0, #448]
	ldr x8, [x0, #272]
	eor x8, x8, x16
	mul x9, x8, x6
	umulh x10, x8, x6
	adds x1, x2, x9
	adc x2, x12, x10
	ldr x8, [x0, #304]
	eor x8, x8, x17
	mul x9, x8, x7
	umulh x10, x8, x7
	adds x1, x1, x9
	adc x2, x2, x10
	str x1, [x0, #456]
	ldr x8, [x0, #280]
	eor x8, x8, x16
	and x3, x16, x6
	sub x3, x12, x3
	mul x9, x8, x6
	umulh x10, x8, x6
	adds x1, x2, x9
	adc x3, x3, x10
	ldr x8, [x0, #312]
	eor x8, x8, x17
	and x2, x17, x7
	sub x2, x12, x2
	add x3, x3, x2
	mul x9, x8, x7
	umulh x10, x8, x7
	adds x1, x1, x9
	adc x3, x3, x10
	str x1, [x0, #464]
	str x3, [x0, #472]
	ldr x1, [x0, #320]
	ldr x2, [x0, #328]
	ldr x3, [x0, #336]
	ldr x8, [x0, #344]
	ldr x9, [x0, #352]
	extr x1, x2, x1, #59
	extr x2, x3, x2, #59
	extr x3, x8, x3, #59
	extr x8, x9, x8, #59
	str x1, [x0, #192]
	str x2, [x0, #200]
	str x3, [x0, #208]
	str x8, [x0, #216]
	ldr x1, [x0, #360]
	ldr x2, [x0, #368]
	ldr x3, [x0, #376]
	ldr x8, [x0, #384]
	ldr x9, [x0, #392]
	extr x1, x2, x1, #59
	extr x2, x3, x2, #59
	extr x3, x8, x3, #59
	extr x8, x9, x8, #59
	str x1, [x0, #224]
	str x2, [x0, #232]
	str x3, [x0, #240]
	str x8, [x0, #248]
	movz x13, #19, lsl #0
	ldr x1, [x0, #400]
	ldr x2, [x0, #408]
	ldr x3, [x0, #416]
	ldr x8, [x0, #424]
	ldr x9, [x0, #432]
	extr x10, x9, x8, #63
	lsr x11, x9, #63
	sub x10, x10, x11
	lsl x11, x10, #63
	add x8, x8, x11
	lsr x14, x10, #63
	sub x14, x12, x14
	mul x9, x10, x13
	umulh x11, x10, x13
	and x15, x14, x13
	sub x11, x11, x15
	adds x1, x1, x9
	adcs x2, x2, x11
	adcs x3, x3, x14
	adc x8, x8, x14
	str x1, [x0, #256]
	str x2, [x0, #264]
	str x3, [x0, #272]
	str x8, [x0, #280]
	ldr x1, [x0, #440]
	ldr x2, [x0, #448]
	ldr x3, [x0, #456]
	ldr x8, [x0, #464]
	ldr x9, [x0, #472]
	extr x10, x9, x8, #63
	lsr x11, x9, #63
	sub x10, x10, x11
	lsl x11, x10, #63
	add x8, x8, x11
	lsr x14, x10, #63
	sub x14, x12, x14
	mul x9, x10, x13
	umulh x11, x10, x13
	and x15, x14, x13
	sub x11, x11, x15
	adds x1, x1, x9
	adcs x2, x2, x11
	adcs x3, x3, x14
	adc x8, x8, x14
	str x1, [x0, #288]
	str x2, [x0, #296]
	str x3, [x0, #304]
	str x8, [x0, #312]
	sub x20, x20, #1
	cbnz x20, 21b
	movz x12, #0, lsl #0
	movz x6, #19, lsl #0
	movz x7, #65535, lsl #0
	movk x7, #65535, lsl #16
	movk x7, #65535, lsl #32
	movk x7, #32767, lsl #48
	ldr x2, [x0, #256]
	ldr x3, [x0, #264]
	ldr x4, [x0, #272]
	ldr x5, [x0, #280]
	lsr x8, x5, #63
	and x5, x5, x7
	mul x8, x8, x6
	adds x2, x2, x8
	adcs x3, x3, x12
	adcs x4, x4, x12
	adc x5, x5, x12
	movz x9, #65498, lsl #0
	movk x9, #65535, lsl #16
	movk x9, #65535, lsl #32
	movk x9, #65535, lsl #48
	movz x10, #65535, lsl #0
	movk x10, #65535, lsl #16
	movk x10, #65535, lsl #32
	movk x10, #65535, lsl #48
	subs x8, x9, x2
	sbcs x9, x10, x3
	sbcs x11, x10, x4
	sbc x10, x10, x5
	ldr x13, [x0, #216]
	lsr x13, x13, #63
	sub x13, x12, x13
	eor x8, x8, x2
	and x8, x8, x13
	eor x2, x2, x8
	eor x9, x9, x3
	and x9, x9, x13
	eor x3, x3, x9
	eor x11, x11, x4
	and x11, x11, x13
	eor x4, x4, x11
	eor x10, x10, x5
	and x10, x10, x13
	eor x5, x5, x10
	str x2, [x0, #544]
	str x3, [x0, #552]
	str x4, [x0, #560]
	str x5, [x0, #568]
	add x1, x19, #0
	movz w10, #0, lsl #0
	ldr x12, [x0, #544]
	ldr x13, [x0, #552]
	ldr x14, [x0, #560]
	ldr x15, [x0, #568]
	ldr x3, [x0, #96]
	mul x4, x3, x12
	mul x5, x3, x13
	mul x6, x3, x14
	mul x7, x3, x15
	umulh x2, x3, x12
	umulh x8, x3, x13
	umulh x9, x3, x14
	umulh x16, x3, x15
	adds x5, x5, x2
	adcs x6, x6, x8
	adcs x7, x7, x9
	adcs x21, x16, x10
	ldr x3, [x0, #104]
	mul x2, x3, x12
	mul x8, x3, x13
	mul x9, x3, x14
	mul x16, x3, x15
	adds x5, x5, x2
	adcs x6, x6, x8
	adcs x7, x7, x9
	adcs x21, x21, x16
	adcs x22, x10, x10
	umulh x2, x3, x12
	umulh x8, x3, x13
	umulh x9, x3, x14
	umulh x16, x3, x15
	adds x6, x6, x2
	adcs x7, x7, x8
	adcs x21, x21, x9
	adcs x22, x22, x16
	ldr x3, [x0, #112]
	mul x2, x3, x12
	mul x8, x3, x13
	mul x9, x3, x14
	mul x16, x3, x15
	adds x6, x6, x2
	adcs x7, x7, x8
	adcs x21, x21, x9
	adcs x22, x22, x16
	adcs x23, x10, x10
	umulh x2, x3, x12
	umulh x8, x3, x13
	umulh x9, x3, x14
	umulh x16, x3, x15
	adds x7, x7, x2
	adcs x21, x21, x8
	adcs x22, x22, x9
	adcs x23, x23, x16
	ldr x3, [x0, #120]
	mul x2, x3, x12
	mul x8, x3, x13
	mul x9, x3, x14
	mul x16, x3, x15
	adds x7, x7, x2
	adcs x21, x21, x8
	adcs x22, x22, x9
	adcs x23, x23, x16
	adcs x24, x10, x10
	umulh x2, x3, x12
	umulh x8, x3, x13
	umulh x9, x3, x14
	umulh x16, x3, x15
	adds x21, x21, x2
	adcs x22, x22, x8
	adcs x23, x23, x9
	adcs x24, x24, x16
	movz w11, #38, lsl #0
	mul x2, x11, x21
	adds x4, x4, x2
	mul x8, x11, x22
	adcs x5, x5, x8
	mul x9, x11, x23
	adcs x6, x6, x9
	mul x16, x11, x24
	adcs x7, x7, x16
	adcs x20, x10, x10
	umulh x2, x11, x21
	umulh x8, x11, x22
	umulh x9, x11, x23
	umulh x16, x11, x24
	adds x7, x7, x9
	adcs x20, x20, x16
	adds x16, x7, x7
	adc x9, x20, x20
	lsr x7, x16, #1
	movz w11, #19, lsl #0
	mul x9, x9, x11
	adds x4, x4, x9
	adcs x5, x5, x2
	adcs x6, x6, x8
	adcs x7, x7, x10
	str x4, [x0, #96]
	str x5, [x0, #104]
	str x6, [x0, #112]
	str x7, [x0, #120]
	movz w10, #0, lsl #0
	movz w11, #19, lsl #0
	movz x2, #65535, lsl #0
	movk x2, #65535, lsl #16
	movk x2, #65535, lsl #32
	movk x2, #32767, lsl #48
	ldr x4, [x0, #96]
	ldr x5, [x0, #104]
	ldr x6, [x0, #112]
	ldr x7, [x0, #120]
	lsr x8, x7, #63
	and x7, x7, x2
	mul x3, x8, x11
	adds x4, x4, x3
	adcs x5, x5, x10
	adcs x6, x6, x10
	adcs x7, x7, x10
	adds x21, x4, x11
	adcs x22, x5, x10
	adcs x23, x6, x10
	adcs x24, x7, x10
	lsr x8, x24, #63
	and x24, x24, x2
	sub x3, x10, x8
	eor x21, x21, x4
	and x21, x21, x3
	eor x4, x4, x21
	eor x22, x22, x5
	and x22, x22, x3
	eor x5, x5, x22
	eor x23, x23, x6
	and x23, x23, x3
	eor x6, x6, x23
	eor x24, x24, x7
	and x24, x24, x3
	eor x7, x7, x24
	str x4, [x1, #0]
	str x5, [x1, #8]
	str x6, [x1, #16]
	str x7, [x1, #24]
	ldr x19, [x0, #0]
	ldr x20, [x0, #8]
	ldr x21, [x0, #16]
	ldr x22, [x0, #24]
	ldr x23, [x0, #32]
	ldr x24, [x0, #40]
	ret
	.p2align 6

vg_x25519_base:
	str x19, [x2, #0]
	str x20, [x2, #8]
	str x21, [x2, #16]
	str x22, [x2, #24]
	str x23, [x2, #32]
	str x24, [x2, #40]
	str x0, [x2, #48]
	add x0, x2, #0
	movz w19, #0, lsl #0
	movz w11, #1, lsl #0
20:
	add x8, x1, x19
	ldrb w8, [x8, #0]
	lsl x9, x19, #3
	add x9, x0, x9
	lsr x2, x8, #0
	and x2, x2, x11
	strb w2, [x9, #768]
	lsr x2, x8, #1
	and x2, x2, x11
	strb w2, [x9, #769]
	lsr x2, x8, #2
	and x2, x2, x11
	strb w2, [x9, #770]
	lsr x2, x8, #3
	and x2, x2, x11
	strb w2, [x9, #771]
	lsr x2, x8, #4
	and x2, x2, x11
	strb w2, [x9, #772]
	lsr x2, x8, #5
	and x2, x2, x11
	strb w2, [x9, #773]
	lsr x2, x8, #6
	and x2, x2, x11
	strb w2, [x9, #774]
	lsr x2, x8, #7
	and x2, x2, x11
	strb w2, [x9, #775]
	add x19, x19, #1
	movz x8, #32, lsl #0
	movk x8, #0, lsl #16
	movk x8, #0, lsl #32
	movk x8, #0, lsl #48
	sub x8, x19, x8
	cbnz x8, 20b
	movz w9, #0, lsl #0
	strb w9, [x0, #768]
	strb w9, [x0, #769]
	strb w9, [x0, #770]
	strb w9, [x0, #1023]
	movz w9, #1, lsl #0
	strb w9, [x0, #1022]
	movz x4, #0, lsl #0
	movk x4, #0, lsl #16
	movk x4, #0, lsl #32
	movk x4, #0, lsl #48
	movz x5, #0, lsl #0
	movk x5, #0, lsl #16
	movk x5, #0, lsl #32
	movk x5, #0, lsl #48
	movz x6, #0, lsl #0
	movk x6, #0, lsl #16
	movk x6, #0, lsl #32
	movk x6, #0, lsl #48
	movz x7, #0, lsl #0
	movk x7, #0, lsl #16
	movk x7, #0, lsl #32
	movk x7, #0, lsl #48
	str x4, [x0, #736]
	str x5, [x0, #744]
	str x6, [x0, #752]
	str x7, [x0, #760]
	movz x4, #19732, lsl #0
	movk x4, #3704, lsl #16
	movk x4, #12927, lsl #32
	movk x4, #9506, lsl #48
	movz x5, #5405, lsl #0
	movk x5, #45271, lsl #16
	movk x5, #55882, lsl #32
	movk x5, #3292, lsl #48
	movz x6, #56252, lsl #0
	movk x6, #36121, lsl #16
	movk x6, #1244, lsl #32
	movk x6, #24478, lsl #48
	movz x7, #6932, lsl #0
	movk x7, #13402, lsl #16
	movk x7, #62822, lsl #32
	movk x7, #2631, lsl #48
	str x4, [x0, #64]
	str x5, [x0, #72]
	str x6, [x0, #80]
	str x7, [x0, #88]
	movz x4, #63212, lsl #0
	movk x4, #7152, lsl #16
	movk x4, #46503, lsl #32
	movk x4, #42296, lsl #48
	movz x5, #22843, lsl #0
	movk x5, #23337, lsl #16
	movk x5, #47280, lsl #32
	movk x5, #5943, lsl #48
	movz x6, #51705, lsl #0
	movk x6, #39721, lsl #16
	movk x6, #22935, lsl #32
	movk x6, #12652, lsl #48
	movz x7, #638, lsl #0
	movk x7, #13703, lsl #16
	movk x7, #18230, lsl #32
	movk x7, #2371, lsl #48
	str x4, [x0, #96]
	str x5, [x0, #104]
	str x6, [x0, #112]
	str x7, [x0, #120]
	movz x4, #1, lsl #0
	movk x4, #0, lsl #16
	movk x4, #0, lsl #32
	movk x4, #0, lsl #48
	movz x5, #0, lsl #0
	movk x5, #0, lsl #16
	movk x5, #0, lsl #32
	movk x5, #0, lsl #48
	movz x6, #0, lsl #0
	movk x6, #0, lsl #16
	movk x6, #0, lsl #32
	movk x6, #0, lsl #48
	movz x7, #0, lsl #0
	movk x7, #0, lsl #16
	movk x7, #0, lsl #32
	movk x7, #0, lsl #48
	str x4, [x0, #128]
	str x5, [x0, #136]
	str x6, [x0, #144]
	str x7, [x0, #152]
	movz x4, #21093, lsl #0
	movk x4, #17697, lsl #16
	movk x4, #18186, lsl #32
	movk x4, #52560, lsl #48
	movz x5, #40439, lsl #0
	movk x5, #3071, lsl #16
	movk x5, #8693, lsl #32
	movk x5, #63940, lsl #48
	movz x6, #32329, lsl #0
	movk x6, #58054, lsl #16
	movk x6, #33041, lsl #32
	movk x6, #3634, lsl #48
	movz x7, #49440, lsl #0
	movk x7, #53819, lsl #16
	movk x7, #38278, lsl #32
	movk x7, #14477, lsl #48
	str x4, [x0, #160]
	str x5, [x0, #168]
	str x6, [x0, #176]
	str x7, [x0, #184]
	ldrb w2, [x0, #771]
	sub x1, x2, #1
	movz x4, #60534, lsl #0
	movk x4, #53922, lsl #16
	movk x4, #56770, lsl #32
	movk x4, #11343, lsl #48
	movz x5, #26177, lsl #0
	movk x5, #53155, lsl #16
	movk x5, #38665, lsl #32
	movk x5, #43305, lsl #48
	movz x6, #10350, lsl #0
	movk x6, #42731, lsl #16
	movk x6, #831, lsl #32
	movk x6, #56923, lsl #48
	movz x7, #55776, lsl #0
	movk x7, #51424, lsl #16
	movk x7, #57395, lsl #32
	movk x7, #1722, lsl #48
	ldr x12, [x0, #64]
	ldr x13, [x0, #72]
	ldr x14, [x0, #80]
	ldr x15, [x0, #88]
	tst x1, x1
	csel x4, x4, x12, ne
	csel x5, x5, x13, ne
	csel x6, x6, x14, ne
	csel x7, x7, x15, ne
	str x4, [x0, #64]
	str x5, [x0, #72]
	str x6, [x0, #80]
	str x7, [x0, #88]
	movz x4, #40353, lsl #0
	movk x4, #16634, lsl #16
	movk x4, #28957, lsl #32
	movk x4, #37013, lsl #48
	movz x5, #57866, lsl #0
	movk x5, #26512, lsl #16
	movk x5, #1863, lsl #32
	movk x5, #44137, lsl #48
	movz x6, #3309, lsl #0
	movk x6, #56451, lsl #16
	movk x6, #11588, lsl #32
	movk x6, #42988, lsl #48
	movz x7, #32823, lsl #0
	movk x7, #59365, lsl #16
	movk x7, #19103, lsl #32
	movk x7, #9272, lsl #48
	ldr x12, [x0, #96]
	ldr x13, [x0, #104]
	ldr x14, [x0, #112]
	ldr x15, [x0, #120]
	tst x1, x1
	csel x4, x4, x12, ne
	csel x5, x5, x13, ne
	csel x6, x6, x14, ne
	csel x7, x7, x15, ne
	str x4, [x0, #96]
	str x5, [x0, #104]
	str x6, [x0, #112]
	str x7, [x0, #120]
	movz x4, #42938, lsl #0
	movk x4, #55071, lsl #16
	movk x4, #37756, lsl #32
	movk x4, #21366, lsl #48
	movz x5, #6273, lsl #0
	movk x5, #49204, lsl #16
	movk x5, #65420, lsl #32
	movk x5, #15643, lsl #48
	movz x6, #36774, lsl #0
	movk x6, #17198, lsl #16
	movk x6, #62726, lsl #32
	movk x6, #8567, lsl #48
	movz x7, #12681, lsl #0
	movk x7, #25759, lsl #16
	movk x7, #61128, lsl #32
	movk x7, #7039, lsl #48
	ldr x12, [x0, #160]
	ldr x13, [x0, #168]
	ldr x14, [x0, #176]
	ldr x15, [x0, #184]
	tst x1, x1
	csel x4, x4, x12, ne
	csel x5, x5, x13, ne
	csel x6, x6, x14, ne
	csel x7, x7, x15, ne
	str x4, [x0, #160]
	str x5, [x0, #168]
	str x6, [x0, #176]
	str x7, [x0, #184]
	movz w19, #1, lsl #0
21:
	lsl x8, x19, #2
	add x8, x0, x8
	ldrb w2, [x8, #771]
	add x2, x2, x2
	ldrb w3, [x8, #770]
	add x2, x2, x3
	add x2, x2, x2
	ldrb w3, [x8, #769]
	add x2, x2, x3
	add x2, x2, x2
	ldrb w3, [x8, #768]
	add x2, x2, x3
	sub x3, x2, #8
	lsr x1, x3, #63
	movz w9, #0, lsl #0
	sub x1, x9, x1
	eor x2, x3, x1
	sub x2, x2, x1
	adrp x9, {VG_ED25519_COMB}
	add x9, x9, {VG_ED25519_COMB}
	lsl x16, x19, #8
	add x9, x9, x16
	add x9, x9, x16
	add x9, x9, x16
	movz x3, #1, lsl #0
	movz x4, #0, lsl #0
	movz x5, #0, lsl #0
	movz x6, #0, lsl #0
	movz x7, #1, lsl #0
	movz x8, #0, lsl #0
	movz x10, #0, lsl #0
	movz x11, #0, lsl #0
	movz x12, #0, lsl #0
	movz x13, #0, lsl #0
	movz x14, #0, lsl #0
	movz x15, #0, lsl #0
	movz x16, #1, lsl #0
	subs x16, x2, x16
	ldp x16, x17, [x9, #0]
	csel x3, x16, x3, eq
	csel x4, x17, x4, eq
	ldp x16, x17, [x9, #16]
	csel x5, x16, x5, eq
	csel x6, x17, x6, eq
	ldp x16, x17, [x9, #256]
	csel x7, x16, x7, eq
	csel x8, x17, x8, eq
	ldp x16, x17, [x9, #272]
	csel x10, x16, x10, eq
	csel x11, x17, x11, eq
	movz x16, #2, lsl #0
	subs x16, x2, x16
	ldp x16, x17, [x9, #32]
	csel x3, x16, x3, eq
	csel x4, x17, x4, eq
	ldp x16, x17, [x9, #48]
	csel x5, x16, x5, eq
	csel x6, x17, x6, eq
	ldp x16, x17, [x9, #288]
	csel x7, x16, x7, eq
	csel x8, x17, x8, eq
	ldp x16, x17, [x9, #304]
	csel x10, x16, x10, eq
	csel x11, x17, x11, eq
	movz x16, #3, lsl #0
	subs x16, x2, x16
	ldp x16, x17, [x9, #64]
	csel x3, x16, x3, eq
	csel x4, x17, x4, eq
	ldp x16, x17, [x9, #80]
	csel x5, x16, x5, eq
	csel x6, x17, x6, eq
	ldp x16, x17, [x9, #320]
	csel x7, x16, x7, eq
	csel x8, x17, x8, eq
	ldp x16, x17, [x9, #336]
	csel x10, x16, x10, eq
	csel x11, x17, x11, eq
	movz x16, #4, lsl #0
	subs x16, x2, x16
	ldp x16, x17, [x9, #96]
	csel x3, x16, x3, eq
	csel x4, x17, x4, eq
	ldp x16, x17, [x9, #112]
	csel x5, x16, x5, eq
	csel x6, x17, x6, eq
	ldp x16, x17, [x9, #352]
	csel x7, x16, x7, eq
	csel x8, x17, x8, eq
	ldp x16, x17, [x9, #368]
	csel x10, x16, x10, eq
	csel x11, x17, x11, eq
	movz x16, #5, lsl #0
	subs x16, x2, x16
	ldp x16, x17, [x9, #128]
	csel x3, x16, x3, eq
	csel x4, x17, x4, eq
	ldp x16, x17, [x9, #144]
	csel x5, x16, x5, eq
	csel x6, x17, x6, eq
	ldp x16, x17, [x9, #384]
	csel x7, x16, x7, eq
	csel x8, x17, x8, eq
	ldp x16, x17, [x9, #400]
	csel x10, x16, x10, eq
	csel x11, x17, x11, eq
	movz x16, #6, lsl #0
	subs x16, x2, x16
	ldp x16, x17, [x9, #160]
	csel x3, x16, x3, eq
	csel x4, x17, x4, eq
	ldp x16, x17, [x9, #176]
	csel x5, x16, x5, eq
	csel x6, x17, x6, eq
	ldp x16, x17, [x9, #416]
	csel x7, x16, x7, eq
	csel x8, x17, x8, eq
	ldp x16, x17, [x9, #432]
	csel x10, x16, x10, eq
	csel x11, x17, x11, eq
	movz x16, #7, lsl #0
	subs x16, x2, x16
	ldp x16, x17, [x9, #192]
	csel x3, x16, x3, eq
	csel x4, x17, x4, eq
	ldp x16, x17, [x9, #208]
	csel x5, x16, x5, eq
	csel x6, x17, x6, eq
	ldp x16, x17, [x9, #448]
	csel x7, x16, x7, eq
	csel x8, x17, x8, eq
	ldp x16, x17, [x9, #464]
	csel x10, x16, x10, eq
	csel x11, x17, x11, eq
	movz x16, #8, lsl #0
	subs x16, x2, x16
	ldp x16, x17, [x9, #224]
	csel x3, x16, x3, eq
	csel x4, x17, x4, eq
	ldp x16, x17, [x9, #240]
	csel x5, x16, x5, eq
	csel x6, x17, x6, eq
	ldp x16, x17, [x9, #480]
	csel x7, x16, x7, eq
	csel x8, x17, x8, eq
	ldp x16, x17, [x9, #496]
	csel x10, x16, x10, eq
	csel x11, x17, x11, eq
	add x9, x9, #512
	movz x16, #1, lsl #0
	subs x16, x2, x16
	ldp x16, x17, [x9, #0]
	csel x12, x16, x12, eq
	csel x13, x17, x13, eq
	ldp x16, x17, [x9, #16]
	csel x14, x16, x14, eq
	csel x15, x17, x15, eq
	movz x16, #2, lsl #0
	subs x16, x2, x16
	ldp x16, x17, [x9, #32]
	csel x12, x16, x12, eq
	csel x13, x17, x13, eq
	ldp x16, x17, [x9, #48]
	csel x14, x16, x14, eq
	csel x15, x17, x15, eq
	movz x16, #3, lsl #0
	subs x16, x2, x16
	ldp x16, x17, [x9, #64]
	csel x12, x16, x12, eq
	csel x13, x17, x13, eq
	ldp x16, x17, [x9, #80]
	csel x14, x16, x14, eq
	csel x15, x17, x15, eq
	movz x16, #4, lsl #0
	subs x16, x2, x16
	ldp x16, x17, [x9, #96]
	csel x12, x16, x12, eq
	csel x13, x17, x13, eq
	ldp x16, x17, [x9, #112]
	csel x14, x16, x14, eq
	csel x15, x17, x15, eq
	movz x16, #5, lsl #0
	subs x16, x2, x16
	ldp x16, x17, [x9, #128]
	csel x12, x16, x12, eq
	csel x13, x17, x13, eq
	ldp x16, x17, [x9, #144]
	csel x14, x16, x14, eq
	csel x15, x17, x15, eq
	movz x16, #6, lsl #0
	subs x16, x2, x16
	ldp x16, x17, [x9, #160]
	csel x12, x16, x12, eq
	csel x13, x17, x13, eq
	ldp x16, x17, [x9, #176]
	csel x14, x16, x14, eq
	csel x15, x17, x15, eq
	movz x16, #7, lsl #0
	subs x16, x2, x16
	ldp x16, x17, [x9, #192]
	csel x12, x16, x12, eq
	csel x13, x17, x13, eq
	ldp x16, x17, [x9, #208]
	csel x14, x16, x14, eq
	csel x15, x17, x15, eq
	movz x16, #8, lsl #0
	subs x16, x2, x16
	ldp x16, x17, [x9, #224]
	csel x12, x16, x12, eq
	csel x13, x17, x13, eq
	ldp x16, x17, [x9, #240]
	csel x14, x16, x14, eq
	csel x15, x17, x15, eq
	movz x17, #0, lsl #0
	sub x17, x17, #1
	lsr x24, x17, #1
	sub x16, x17, #18
	subs x20, x16, x12
	sbcs x21, x17, x13
	sbcs x22, x17, x14
	sbc x23, x24, x15
	tst x1, x1
	csel x12, x20, x12, ne
	csel x13, x21, x13, ne
	csel x14, x22, x14, ne
	csel x15, x23, x15, ne
	csel x20, x7, x3, ne
	csel x21, x8, x4, ne
	csel x22, x10, x5, ne
	csel x23, x11, x6, ne
	csel x16, x3, x7, ne
	csel x17, x4, x8, ne
	csel x24, x5, x10, ne
	csel x2, x6, x11, ne
	stp x20, x21, [x0, #192]
	stp x22, x23, [x0, #208]
	stp x16, x17, [x0, #224]
	stp x24, x2, [x0, #240]
	stp x12, x13, [x0, #256]
	stp x14, x15, [x0, #272]
	movz x17, #0, lsl #0
	ldp x3, x4, [x0, #128]
	ldp x7, x8, [x0, #128]
	adds x3, x3, x7
	adcs x4, x4, x8
	ldp x5, x6, [x0, #144]
	ldp x7, x8, [x0, #144]
	adcs x5, x5, x7
	adcs x6, x6, x8
	movz w9, #38, lsl #0
	csel x9, x9, x17, hs
	adds x3, x3, x9
	adcs x4, x4, x17
	adcs x5, x5, x17
	adc x6, x6, x17
	stp x3, x4, [x0, #288]
	stp x5, x6, [x0, #304]
	ldp x5, x6, [x0, #96]
	ldp x4, x3, [x0, #64]
	subs x5, x5, x4
	sbcs x6, x6, x3
	ldp x7, x8, [x0, #112]
	ldp x4, x3, [x0, #80]
	sbcs x7, x7, x4
	sbcs x8, x8, x3
	movz w4, #38, lsl #0
	csel x3, x4, x17, lo
	subs x5, x5, x3
	sbcs x6, x6, x17
	sbcs x7, x7, x17
	sbc x8, x8, x17
	stp x5, x6, [x0, #320]
	stp x7, x8, [x0, #336]
	ldp x3, x4, [x0, #96]
	ldp x7, x8, [x0, #64]
	adds x3, x3, x7
	adcs x4, x4, x8
	ldp x5, x6, [x0, #112]
	ldp x7, x8, [x0, #80]
	adcs x5, x5, x7
	adcs x6, x6, x8
	movz w9, #38, lsl #0
	csel x9, x9, x17, hs
	adds x3, x3, x9
	adcs x4, x4, x17
	adcs x5, x5, x17
	adc x6, x6, x17
	stp x3, x4, [x0, #352]
	stp x5, x6, [x0, #368]
	ldp x3, x4, [x0, #160]
	ldp x7, x8, [x0, #256]
	mul x12, x3, x7
	umulh x13, x3, x7
	mul x11, x3, x8
	umulh x14, x3, x8
	adds x13, x13, x11
	ldp x9, x10, [x0, #272]
	mul x11, x3, x9
	umulh x15, x3, x9
	adcs x14, x14, x11
	mul x11, x3, x10
	umulh x16, x3, x10
	adcs x15, x15, x11
	adc x16, x16, x17
	ldp x5, x6, [x0, #176]
	mul x11, x4, x7
	adds x13, x13, x11
	mul x11, x4, x8
	adcs x14, x14, x11
	mul x11, x4, x9
	adcs x15, x15, x11
	mul x11, x4, x10
	adcs x16, x16, x11
	umulh x3, x4, x10
	adc x3, x3, x17
	umulh x11, x4, x7
	adds x14, x14, x11
	umulh x11, x4, x8
	adcs x15, x15, x11
	umulh x11, x4, x9
	adcs x16, x16, x11
	adc x3, x3, x17
	mul x11, x5, x7
	adds x14, x14, x11
	mul x11, x5, x8
	adcs x15, x15, x11
	mul x11, x5, x9
	adcs x16, x16, x11
	mul x11, x5, x10
	adcs x3, x3, x11
	umulh x4, x5, x10
	adc x4, x4, x17
	umulh x11, x5, x7
	adds x15, x15, x11
	umulh x11, x5, x8
	adcs x16, x16, x11
	umulh x11, x5, x9
	adcs x3, x3, x11
	adc x4, x4, x17
	mul x11, x6, x7
	adds x15, x15, x11
	mul x11, x6, x8
	adcs x16, x16, x11
	mul x11, x6, x9
	adcs x3, x3, x11
	mul x11, x6, x10
	adcs x4, x4, x11
	umulh x5, x6, x10
	adc x5, x5, x17
	umulh x11, x6, x7
	adds x16, x16, x11
	umulh x11, x6, x8
	adcs x3, x3, x11
	umulh x11, x6, x9
	adcs x4, x4, x11
	adc x5, x5, x17
	movz w7, #38, lsl #0
	mul x11, x7, x16
	umulh x9, x7, x16
	adds x12, x12, x11
	mul x11, x7, x3
	umulh x3, x7, x3
	adcs x13, x13, x11
	mul x11, x7, x4
	umulh x4, x7, x4
	adcs x14, x14, x11
	mul x11, x7, x5
	umulh x5, x7, x5
	adcs x15, x15, x11
	adc x16, x17, x17
	adds x15, x15, x4
	adc x16, x16, x5
	adds x11, x15, x15
	lsr x15, x11, #1
	adc x8, x16, x16
	movz w7, #19, lsl #0
	mul x11, x7, x8
	adds x12, x12, x11
	adcs x13, x13, x9
	adcs x14, x14, x3
	adc x15, x15, x17
	stp x12, x13, [x0, #384]
	stp x14, x15, [x0, #400]
	ldp x3, x4, [x0, #320]
	ldp x7, x8, [x0, #192]
	mul x12, x3, x7
	umulh x13, x3, x7
	mul x11, x3, x8
	umulh x14, x3, x8
	adds x13, x13, x11
	ldp x9, x10, [x0, #208]
	mul x11, x3, x9
	umulh x15, x3, x9
	adcs x14, x14, x11
	mul x11, x3, x10
	umulh x16, x3, x10
	adcs x15, x15, x11
	adc x16, x16, x17
	ldp x5, x6, [x0, #336]
	mul x11, x4, x7
	adds x13, x13, x11
	mul x11, x4, x8
	adcs x14, x14, x11
	mul x11, x4, x9
	adcs x15, x15, x11
	mul x11, x4, x10
	adcs x16, x16, x11
	umulh x3, x4, x10
	adc x3, x3, x17
	umulh x11, x4, x7
	adds x14, x14, x11
	umulh x11, x4, x8
	adcs x15, x15, x11
	umulh x11, x4, x9
	adcs x16, x16, x11
	adc x3, x3, x17
	mul x11, x5, x7
	adds x14, x14, x11
	mul x11, x5, x8
	adcs x15, x15, x11
	mul x11, x5, x9
	adcs x16, x16, x11
	mul x11, x5, x10
	adcs x3, x3, x11
	umulh x4, x5, x10
	adc x4, x4, x17
	umulh x11, x5, x7
	adds x15, x15, x11
	umulh x11, x5, x8
	adcs x16, x16, x11
	umulh x11, x5, x9
	adcs x3, x3, x11
	adc x4, x4, x17
	mul x11, x6, x7
	adds x15, x15, x11
	mul x11, x6, x8
	adcs x16, x16, x11
	mul x11, x6, x9
	adcs x3, x3, x11
	mul x11, x6, x10
	adcs x4, x4, x11
	umulh x5, x6, x10
	adc x5, x5, x17
	umulh x11, x6, x7
	adds x16, x16, x11
	umulh x11, x6, x8
	adcs x3, x3, x11
	umulh x11, x6, x9
	adcs x4, x4, x11
	adc x5, x5, x17
	movz w7, #38, lsl #0
	mul x11, x7, x16
	umulh x9, x7, x16
	adds x12, x12, x11
	mul x11, x7, x3
	umulh x3, x7, x3
	adcs x13, x13, x11
	mul x11, x7, x4
	umulh x4, x7, x4
	adcs x14, x14, x11
	mul x11, x7, x5
	umulh x5, x7, x5
	adcs x15, x15, x11
	adc x16, x17, x17
	adds x15, x15, x4
	adc x16, x16, x5
	adds x11, x15, x15
	lsr x15, x11, #1
	adc x8, x16, x16
	movz w7, #19, lsl #0
	mul x11, x7, x8
	adds x12, x12, x11
	adcs x13, x13, x9
	adcs x14, x14, x3
	adc x15, x15, x17
	stp x12, x13, [x0, #320]
	stp x14, x15, [x0, #336]
	ldp x3, x4, [x0, #352]
	ldp x7, x8, [x0, #224]
	mul x12, x3, x7
	umulh x13, x3, x7
	mul x11, x3, x8
	umulh x14, x3, x8
	adds x13, x13, x11
	ldp x9, x10, [x0, #240]
	mul x11, x3, x9
	umulh x15, x3, x9
	adcs x14, x14, x11
	mul x11, x3, x10
	umulh x16, x3, x10
	adcs x15, x15, x11
	adc x16, x16, x17
	ldp x5, x6, [x0, #368]
	mul x11, x4, x7
	adds x13, x13, x11
	mul x11, x4, x8
	adcs x14, x14, x11
	mul x11, x4, x9
	adcs x15, x15, x11
	mul x11, x4, x10
	adcs x16, x16, x11
	umulh x3, x4, x10
	adc x3, x3, x17
	umulh x11, x4, x7
	adds x14, x14, x11
	umulh x11, x4, x8
	adcs x15, x15, x11
	umulh x11, x4, x9
	adcs x16, x16, x11
	adc x3, x3, x17
	mul x11, x5, x7
	adds x14, x14, x11
	mul x11, x5, x8
	adcs x15, x15, x11
	mul x11, x5, x9
	adcs x16, x16, x11
	mul x11, x5, x10
	adcs x3, x3, x11
	umulh x4, x5, x10
	adc x4, x4, x17
	umulh x11, x5, x7
	adds x15, x15, x11
	umulh x11, x5, x8
	adcs x16, x16, x11
	umulh x11, x5, x9
	adcs x3, x3, x11
	adc x4, x4, x17
	mul x11, x6, x7
	adds x15, x15, x11
	mul x11, x6, x8
	adcs x16, x16, x11
	mul x11, x6, x9
	adcs x3, x3, x11
	mul x11, x6, x10
	adcs x4, x4, x11
	umulh x5, x6, x10
	adc x5, x5, x17
	umulh x11, x6, x7
	adds x16, x16, x11
	umulh x11, x6, x8
	adcs x3, x3, x11
	umulh x11, x6, x9
	adcs x4, x4, x11
	adc x5, x5, x17
	movz w7, #38, lsl #0
	mul x11, x7, x16
	umulh x9, x7, x16
	adds x12, x12, x11
	mul x11, x7, x3
	umulh x3, x7, x3
	adcs x13, x13, x11
	mul x11, x7, x4
	umulh x4, x7, x4
	adcs x14, x14, x11
	mul x11, x7, x5
	umulh x5, x7, x5
	adcs x15, x15, x11
	adc x16, x17, x17
	adds x15, x15, x4
	adc x16, x16, x5
	adds x11, x15, x15
	lsr x15, x11, #1
	adc x8, x16, x16
	movz w7, #19, lsl #0
	mul x11, x7, x8
	adds x12, x12, x11
	adcs x13, x13, x9
	adcs x14, x14, x3
	adc x15, x15, x17
	stp x12, x13, [x0, #352]
	stp x14, x15, [x0, #368]
	ldp x5, x6, [x0, #288]
	ldp x4, x3, [x0, #384]
	subs x5, x5, x4
	sbcs x6, x6, x3
	ldp x7, x8, [x0, #304]
	ldp x4, x3, [x0, #400]
	sbcs x7, x7, x4
	sbcs x8, x8, x3
	movz w4, #38, lsl #0
	csel x3, x4, x17, lo
	subs x5, x5, x3
	sbcs x6, x6, x17
	sbcs x7, x7, x17
	sbc x8, x8, x17
	stp x5, x6, [x0, #416]
	stp x7, x8, [x0, #432]
	ldp x3, x4, [x0, #288]
	ldp x7, x8, [x0, #384]
	adds x3, x3, x7
	adcs x4, x4, x8
	ldp x5, x6, [x0, #304]
	ldp x7, x8, [x0, #400]
	adcs x5, x5, x7
	adcs x6, x6, x8
	movz w9, #38, lsl #0
	csel x9, x9, x17, hs
	adds x3, x3, x9
	adcs x4, x4, x17
	adcs x5, x5, x17
	adc x6, x6, x17
	stp x3, x4, [x0, #288]
	stp x5, x6, [x0, #304]
	ldp x5, x6, [x0, #352]
	ldp x4, x3, [x0, #320]
	subs x5, x5, x4
	sbcs x6, x6, x3
	ldp x7, x8, [x0, #368]
	ldp x4, x3, [x0, #336]
	sbcs x7, x7, x4
	sbcs x8, x8, x3
	movz w4, #38, lsl #0
	csel x3, x4, x17, lo
	subs x5, x5, x3
	sbcs x6, x6, x17
	sbcs x7, x7, x17
	sbc x8, x8, x17
	stp x5, x6, [x0, #448]
	stp x7, x8, [x0, #464]
	ldp x3, x4, [x0, #352]
	ldp x7, x8, [x0, #320]
	adds x3, x3, x7
	adcs x4, x4, x8
	ldp x5, x6, [x0, #368]
	ldp x7, x8, [x0, #336]
	adcs x5, x5, x7
	adcs x6, x6, x8
	movz w9, #38, lsl #0
	csel x9, x9, x17, hs
	adds x3, x3, x9
	adcs x4, x4, x17
	adcs x5, x5, x17
	adc x6, x6, x17
	stp x3, x4, [x0, #320]
	stp x5, x6, [x0, #336]
	ldp x3, x4, [x0, #416]
	ldp x7, x8, [x0, #288]
	mul x12, x3, x7
	umulh x13, x3, x7
	mul x11, x3, x8
	umulh x14, x3, x8
	adds x13, x13, x11
	ldp x9, x10, [x0, #304]
	mul x11, x3, x9
	umulh x15, x3, x9
	adcs x14, x14, x11
	mul x11, x3, x10
	umulh x16, x3, x10
	adcs x15, x15, x11
	adc x16, x16, x17
	ldp x5, x6, [x0, #432]
	mul x11, x4, x7
	adds x13, x13, x11
	mul x11, x4, x8
	adcs x14, x14, x11
	mul x11, x4, x9
	adcs x15, x15, x11
	mul x11, x4, x10
	adcs x16, x16, x11
	umulh x3, x4, x10
	adc x3, x3, x17
	umulh x11, x4, x7
	adds x14, x14, x11
	umulh x11, x4, x8
	adcs x15, x15, x11
	umulh x11, x4, x9
	adcs x16, x16, x11
	adc x3, x3, x17
	mul x11, x5, x7
	adds x14, x14, x11
	mul x11, x5, x8
	adcs x15, x15, x11
	mul x11, x5, x9
	adcs x16, x16, x11
	mul x11, x5, x10
	adcs x3, x3, x11
	umulh x4, x5, x10
	adc x4, x4, x17
	umulh x11, x5, x7
	adds x15, x15, x11
	umulh x11, x5, x8
	adcs x16, x16, x11
	umulh x11, x5, x9
	adcs x3, x3, x11
	adc x4, x4, x17
	mul x11, x6, x7
	adds x15, x15, x11
	mul x11, x6, x8
	adcs x16, x16, x11
	mul x11, x6, x9
	adcs x3, x3, x11
	mul x11, x6, x10
	adcs x4, x4, x11
	umulh x5, x6, x10
	adc x5, x5, x17
	umulh x11, x6, x7
	adds x16, x16, x11
	umulh x11, x6, x8
	adcs x3, x3, x11
	umulh x11, x6, x9
	adcs x4, x4, x11
	adc x5, x5, x17
	movz w7, #38, lsl #0
	mul x11, x7, x16
	umulh x9, x7, x16
	adds x12, x12, x11
	mul x11, x7, x3
	umulh x3, x7, x3
	adcs x13, x13, x11
	mul x11, x7, x4
	umulh x4, x7, x4
	adcs x14, x14, x11
	mul x11, x7, x5
	umulh x5, x7, x5
	adcs x15, x15, x11
	adc x16, x17, x17
	adds x15, x15, x4
	adc x16, x16, x5
	adds x11, x15, x15
	lsr x15, x11, #1
	adc x8, x16, x16
	movz w7, #19, lsl #0
	mul x11, x7, x8
	adds x12, x12, x11
	adcs x13, x13, x9
	adcs x14, x14, x3
	adc x15, x15, x17
	stp x12, x13, [x0, #128]
	stp x14, x15, [x0, #144]
	ldp x3, x4, [x0, #448]
	ldp x7, x8, [x0, #416]
	mul x12, x3, x7
	umulh x13, x3, x7
	mul x11, x3, x8
	umulh x14, x3, x8
	adds x13, x13, x11
	ldp x9, x10, [x0, #432]
	mul x11, x3, x9
	umulh x15, x3, x9
	adcs x14, x14, x11
	mul x11, x3, x10
	umulh x16, x3, x10
	adcs x15, x15, x11
	adc x16, x16, x17
	ldp x5, x6, [x0, #464]
	mul x11, x4, x7
	adds x13, x13, x11
	mul x11, x4, x8
	adcs x14, x14, x11
	mul x11, x4, x9
	adcs x15, x15, x11
	mul x11, x4, x10
	adcs x16, x16, x11
	umulh x3, x4, x10
	adc x3, x3, x17
	umulh x11, x4, x7
	adds x14, x14, x11
	umulh x11, x4, x8
	adcs x15, x15, x11
	umulh x11, x4, x9
	adcs x16, x16, x11
	adc x3, x3, x17
	mul x11, x5, x7
	adds x14, x14, x11
	mul x11, x5, x8
	adcs x15, x15, x11
	mul x11, x5, x9
	adcs x16, x16, x11
	mul x11, x5, x10
	adcs x3, x3, x11
	umulh x4, x5, x10
	adc x4, x4, x17
	umulh x11, x5, x7
	adds x15, x15, x11
	umulh x11, x5, x8
	adcs x16, x16, x11
	umulh x11, x5, x9
	adcs x3, x3, x11
	adc x4, x4, x17
	mul x11, x6, x7
	adds x15, x15, x11
	mul x11, x6, x8
	adcs x16, x16, x11
	mul x11, x6, x9
	adcs x3, x3, x11
	mul x11, x6, x10
	adcs x4, x4, x11
	umulh x5, x6, x10
	adc x5, x5, x17
	umulh x11, x6, x7
	adds x16, x16, x11
	umulh x11, x6, x8
	adcs x3, x3, x11
	umulh x11, x6, x9
	adcs x4, x4, x11
	adc x5, x5, x17
	movz w7, #38, lsl #0
	mul x11, x7, x16
	umulh x9, x7, x16
	adds x12, x12, x11
	mul x11, x7, x3
	umulh x3, x7, x3
	adcs x13, x13, x11
	mul x11, x7, x4
	umulh x4, x7, x4
	adcs x14, x14, x11
	mul x11, x7, x5
	umulh x5, x7, x5
	adcs x15, x15, x11
	adc x16, x17, x17
	adds x15, x15, x4
	adc x16, x16, x5
	adds x11, x15, x15
	lsr x15, x11, #1
	adc x8, x16, x16
	movz w7, #19, lsl #0
	mul x11, x7, x8
	adds x12, x12, x11
	adcs x13, x13, x9
	adcs x14, x14, x3
	adc x15, x15, x17
	stp x12, x13, [x0, #64]
	stp x14, x15, [x0, #80]
	ldp x3, x4, [x0, #288]
	ldp x7, x8, [x0, #320]
	mul x12, x3, x7
	umulh x13, x3, x7
	mul x11, x3, x8
	umulh x14, x3, x8
	adds x13, x13, x11
	ldp x9, x10, [x0, #336]
	mul x11, x3, x9
	umulh x15, x3, x9
	adcs x14, x14, x11
	mul x11, x3, x10
	umulh x16, x3, x10
	adcs x15, x15, x11
	adc x16, x16, x17
	ldp x5, x6, [x0, #304]
	mul x11, x4, x7
	adds x13, x13, x11
	mul x11, x4, x8
	adcs x14, x14, x11
	mul x11, x4, x9
	adcs x15, x15, x11
	mul x11, x4, x10
	adcs x16, x16, x11
	umulh x3, x4, x10
	adc x3, x3, x17
	umulh x11, x4, x7
	adds x14, x14, x11
	umulh x11, x4, x8
	adcs x15, x15, x11
	umulh x11, x4, x9
	adcs x16, x16, x11
	adc x3, x3, x17
	mul x11, x5, x7
	adds x14, x14, x11
	mul x11, x5, x8
	adcs x15, x15, x11
	mul x11, x5, x9
	adcs x16, x16, x11
	mul x11, x5, x10
	adcs x3, x3, x11
	umulh x4, x5, x10
	adc x4, x4, x17
	umulh x11, x5, x7
	adds x15, x15, x11
	umulh x11, x5, x8
	adcs x16, x16, x11
	umulh x11, x5, x9
	adcs x3, x3, x11
	adc x4, x4, x17
	mul x11, x6, x7
	adds x15, x15, x11
	mul x11, x6, x8
	adcs x16, x16, x11
	mul x11, x6, x9
	adcs x3, x3, x11
	mul x11, x6, x10
	adcs x4, x4, x11
	umulh x5, x6, x10
	adc x5, x5, x17
	umulh x11, x6, x7
	adds x16, x16, x11
	umulh x11, x6, x8
	adcs x3, x3, x11
	umulh x11, x6, x9
	adcs x4, x4, x11
	adc x5, x5, x17
	movz w7, #38, lsl #0
	mul x11, x7, x16
	umulh x9, x7, x16
	adds x12, x12, x11
	mul x11, x7, x3
	umulh x3, x7, x3
	adcs x13, x13, x11
	mul x11, x7, x4
	umulh x4, x7, x4
	adcs x14, x14, x11
	mul x11, x7, x5
	umulh x5, x7, x5
	adcs x15, x15, x11
	adc x16, x17, x17
	adds x15, x15, x4
	adc x16, x16, x5
	adds x11, x15, x15
	lsr x15, x11, #1
	adc x8, x16, x16
	movz w7, #19, lsl #0
	mul x11, x7, x8
	adds x12, x12, x11
	adcs x13, x13, x9
	adcs x14, x14, x3
	adc x15, x15, x17
	stp x12, x13, [x0, #96]
	stp x14, x15, [x0, #112]
	ldp x3, x4, [x0, #448]
	ldp x7, x8, [x0, #320]
	mul x12, x3, x7
	umulh x13, x3, x7
	mul x11, x3, x8
	umulh x14, x3, x8
	adds x13, x13, x11
	ldp x9, x10, [x0, #336]
	mul x11, x3, x9
	umulh x15, x3, x9
	adcs x14, x14, x11
	mul x11, x3, x10
	umulh x16, x3, x10
	adcs x15, x15, x11
	adc x16, x16, x17
	ldp x5, x6, [x0, #464]
	mul x11, x4, x7
	adds x13, x13, x11
	mul x11, x4, x8
	adcs x14, x14, x11
	mul x11, x4, x9
	adcs x15, x15, x11
	mul x11, x4, x10
	adcs x16, x16, x11
	umulh x3, x4, x10
	adc x3, x3, x17
	umulh x11, x4, x7
	adds x14, x14, x11
	umulh x11, x4, x8
	adcs x15, x15, x11
	umulh x11, x4, x9
	adcs x16, x16, x11
	adc x3, x3, x17
	mul x11, x5, x7
	adds x14, x14, x11
	mul x11, x5, x8
	adcs x15, x15, x11
	mul x11, x5, x9
	adcs x16, x16, x11
	mul x11, x5, x10
	adcs x3, x3, x11
	umulh x4, x5, x10
	adc x4, x4, x17
	umulh x11, x5, x7
	adds x15, x15, x11
	umulh x11, x5, x8
	adcs x16, x16, x11
	umulh x11, x5, x9
	adcs x3, x3, x11
	adc x4, x4, x17
	mul x11, x6, x7
	adds x15, x15, x11
	mul x11, x6, x8
	adcs x16, x16, x11
	mul x11, x6, x9
	adcs x3, x3, x11
	mul x11, x6, x10
	adcs x4, x4, x11
	umulh x5, x6, x10
	adc x5, x5, x17
	umulh x11, x6, x7
	adds x16, x16, x11
	umulh x11, x6, x8
	adcs x3, x3, x11
	umulh x11, x6, x9
	adcs x4, x4, x11
	adc x5, x5, x17
	movz w7, #38, lsl #0
	mul x11, x7, x16
	umulh x9, x7, x16
	adds x12, x12, x11
	mul x11, x7, x3
	umulh x3, x7, x3
	adcs x13, x13, x11
	mul x11, x7, x4
	umulh x4, x7, x4
	adcs x14, x14, x11
	mul x11, x7, x5
	umulh x5, x7, x5
	adcs x15, x15, x11
	adc x16, x17, x17
	adds x15, x15, x4
	adc x16, x16, x5
	adds x11, x15, x15
	lsr x15, x11, #1
	adc x8, x16, x16
	movz w7, #19, lsl #0
	mul x11, x7, x8
	adds x12, x12, x11
	adcs x13, x13, x9
	adcs x14, x14, x3
	adc x15, x15, x17
	stp x12, x13, [x0, #160]
	stp x14, x15, [x0, #176]
	add x19, x19, #1
	sub x8, x19, #64
	cbnz x8, 21b
	movz w10, #0, lsl #0
	movz w11, #38, lsl #0
	ldr x4, [x0, #128]
	ldr x9, [x0, #96]
	adds x4, x4, x9
	ldr x5, [x0, #136]
	ldr x9, [x0, #104]
	adcs x5, x5, x9
	ldr x6, [x0, #144]
	ldr x9, [x0, #112]
	adcs x6, x6, x9
	ldr x7, [x0, #152]
	ldr x9, [x0, #120]
	adcs x7, x7, x9
	csel x8, x11, x10, hs
	adds x4, x4, x8
	adcs x5, x5, x10
	adcs x6, x6, x10
	adcs x7, x7, x10
	csel x8, x11, x10, hs
	add x4, x4, x8
	str x4, [x0, #64]
	str x5, [x0, #72]
	str x6, [x0, #80]
	str x7, [x0, #88]
	movz w10, #0, lsl #0
	movz w11, #38, lsl #0
	ldr x4, [x0, #128]
	ldr x9, [x0, #96]
	subs x4, x4, x9
	ldr x5, [x0, #136]
	ldr x9, [x0, #104]
	sbcs x5, x5, x9
	ldr x6, [x0, #144]
	ldr x9, [x0, #112]
	sbcs x6, x6, x9
	ldr x7, [x0, #152]
	ldr x9, [x0, #120]
	sbcs x7, x7, x9
	sbcs x8, x10, x10
	and x8, x8, x11
	subs x4, x4, x8
	sbcs x5, x5, x10
	sbcs x6, x6, x10
	sbcs x7, x7, x10
	sbcs x8, x10, x10
	and x8, x8, x11
	sub x4, x4, x8
	str x4, [x0, #128]
	str x5, [x0, #136]
	str x6, [x0, #144]
	str x7, [x0, #152]
	add x19, x1, #0
	movz x12, #0, lsl #0
	movz x6, #19, lsl #0
	movz x7, #65535, lsl #0
	movk x7, #65535, lsl #16
	movk x7, #65535, lsl #32
	movk x7, #32767, lsl #48
	ldr x2, [x0, #128]
	ldr x3, [x0, #136]
	ldr x4, [x0, #144]
	ldr x5, [x0, #152]
	lsr x8, x5, #63
	and x5, x5, x7
	mul x8, x8, x6
	adds x2, x2, x8
	adcs x3, x3, x12
	adcs x4, x4, x12
	adc x5, x5, x12
	adds x8, x2, x6
	adcs x9, x3, x12
	adcs x10, x4, x12
	adc x11, x5, x12
	lsr x13, x11, #63
	and x11, x11, x7
	sub x13, x12, x13
	eor x8, x8, x2
	and x8, x8, x13
	eor x2, x2, x8
	eor x9, x9, x3
	and x9, x9, x13
	eor x3, x3, x9
	eor x10, x10, x4
	and x10, x10, x13
	eor x4, x4, x10
	eor x11, x11, x5
	and x11, x11, x13
	eor x5, x5, x11
	str x2, [x0, #224]
	str x3, [x0, #232]
	str x4, [x0, #240]
	str x5, [x0, #248]
	movz x2, #65517, lsl #0
	movk x2, #65535, lsl #16
	movk x2, #65535, lsl #32
	movk x2, #65535, lsl #48
	str x2, [x0, #192]
	movz x2, #65535, lsl #0
	movk x2, #65535, lsl #16
	movk x2, #65535, lsl #32
	movk x2, #65535, lsl #48
	str x2, [x0, #200]
	movz x2, #65535, lsl #0
	movk x2, #65535, lsl #16
	movk x2, #65535, lsl #32
	movk x2, #65535, lsl #48
	str x2, [x0, #208]
	movz x2, #65535, lsl #0
	movk x2, #65535, lsl #16
	movk x2, #65535, lsl #32
	movk x2, #32767, lsl #48
	str x2, [x0, #216]
	str x12, [x0, #256]
	str x12, [x0, #264]
	str x12, [x0, #272]
	str x12, [x0, #280]
	movz x2, #8345, lsl #0
	movk x2, #29954, lsl #16
	movk x2, #40483, lsl #32
	movk x2, #41209, lsl #48
	str x2, [x0, #288]
	movz x2, #9621, lsl #0
	movk x2, #7443, lsl #16
	movk x2, #36671, lsl #32
	movk x2, #43206, lsl #48
	str x2, [x0, #296]
	movz x2, #21058, lsl #0
	movk x2, #1452, lsl #16
	movk x2, #35128, lsl #32
	movk x2, #27756, lsl #48
	str x2, [x0, #304]
	movz x2, #1557, lsl #0
	movk x2, #16759, lsl #16
	movk x2, #2226, lsl #32
	movk x2, #10085, lsl #48
	str x2, [x0, #312]
	movz x1, #1, lsl #0
	str x1, [x0, #480]
	movz x20, #10, lsl #0
22:
	ldr x1, [x0, #480]
	ldr x2, [x0, #192]
	ldr x3, [x0, #224]
	movz x13, #0, lsl #0
	sub x1, x13, x1
	sub x1, x1, #1
	movz x13, #32767, lsl #0
	and x8, x2, x13
	and x9, x3, x13
	movz x16, #32768, lsl #16
	add x8, x8, x16
	movz x16, #32768, lsl #32
	add x9, x9, x16
	movz x12, #1, lsl #0
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x1, #0, #0, ne
	csel x9, x11, x9, mi
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x1, #0, #0, ne
	csel x9, x11, x9, mi
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x1, #0, #0, ne
	csel x9, x11, x9, mi
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x1, #0, #0, ne
	csel x9, x11, x9, mi
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x1, #0, #0, ne
	csel x9, x11, x9, mi
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x1, #0, #0, ne
	csel x9, x11, x9, mi
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x1, #0, #0, ne
	csel x9, x11, x9, mi
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	movz x13, #16384, lsl #16
	movk x13, #8192, lsl #32
	movk x13, #8192, lsl #48
	movz x17, #16384, lsl #0
	add x8, x8, x13
	add x10, x10, x13
	lsr x11, x8, #47
	sub x11, x11, x17
	lsl x8, x8, #17
	lsr x8, x8, #48
	sub x8, x8, x17
	lsr x9, x10, #47
	sub x9, x9, x17
	lsl x10, x10, #17
	lsr x10, x10, #48
	sub x10, x10, x17
	mul x13, x2, x8
	madd x13, x3, x11, x13
	mul x16, x2, x10
	madd x16, x3, x9, x16
	lsr x2, x13, #15
	lsr x3, x16, #15
	orr x4, x8, x8
	orr x5, x11, x11
	orr x6, x10, x10
	orr x7, x9, x9
	movz x13, #32767, lsl #0
	and x8, x2, x13
	and x9, x3, x13
	movz x16, #32768, lsl #16
	add x8, x8, x16
	movz x16, #32768, lsl #32
	add x9, x9, x16
	movz x12, #1, lsl #0
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x1, #0, #0, ne
	csel x9, x11, x9, mi
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x1, #0, #0, ne
	csel x9, x11, x9, mi
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x1, #0, #0, ne
	csel x9, x11, x9, mi
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x1, #0, #0, ne
	csel x9, x11, x9, mi
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x1, #0, #0, ne
	csel x9, x11, x9, mi
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x1, #0, #0, ne
	csel x9, x11, x9, mi
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x1, #0, #0, ne
	csel x9, x11, x9, mi
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	movz x13, #16384, lsl #16
	movk x13, #8192, lsl #32
	movk x13, #8192, lsl #48
	movz x17, #16384, lsl #0
	add x8, x8, x13
	add x10, x10, x13
	lsr x11, x8, #47
	sub x11, x11, x17
	lsl x8, x8, #17
	lsr x8, x8, #48
	sub x8, x8, x17
	lsr x9, x10, #47
	sub x9, x9, x17
	lsl x10, x10, #17
	lsr x10, x10, #48
	sub x10, x10, x17
	mul x13, x2, x8
	madd x13, x3, x11, x13
	mul x16, x2, x10
	madd x16, x3, x9, x16
	lsr x2, x13, #15
	lsr x3, x16, #15
	mul x13, x8, x4
	madd x13, x11, x6, x13
	mul x16, x10, x4
	madd x6, x9, x6, x16
	mul x17, x8, x5
	madd x17, x11, x7, x17
	mul x16, x10, x5
	madd x7, x9, x7, x16
	orr x4, x13, x13
	orr x5, x17, x17
	movz x13, #32767, lsl #0
	and x8, x2, x13
	and x9, x3, x13
	movz x16, #32768, lsl #16
	add x8, x8, x16
	movz x16, #32768, lsl #32
	add x9, x9, x16
	movz x12, #1, lsl #0
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x1, #0, #0, ne
	csel x9, x11, x9, mi
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x1, #0, #0, ne
	csel x9, x11, x9, mi
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x1, #0, #0, ne
	csel x9, x11, x9, mi
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x1, #0, #0, ne
	csel x9, x11, x9, mi
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x1, #0, #0, ne
	csel x9, x11, x9, mi
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x1, #0, #0, ne
	csel x9, x11, x9, mi
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x1, #0, #0, ne
	csel x9, x11, x9, mi
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	movz x13, #16384, lsl #16
	movk x13, #8192, lsl #32
	movk x13, #8192, lsl #48
	movz x17, #16384, lsl #0
	add x8, x8, x13
	add x10, x10, x13
	lsr x11, x8, #47
	sub x11, x11, x17
	lsl x8, x8, #17
	lsr x8, x8, #48
	sub x8, x8, x17
	lsr x9, x10, #47
	sub x9, x9, x17
	lsl x10, x10, #17
	lsr x10, x10, #48
	sub x10, x10, x17
	mul x13, x2, x8
	madd x13, x3, x11, x13
	mul x16, x2, x10
	madd x16, x3, x9, x16
	lsr x2, x13, #15
	lsr x3, x16, #15
	mul x13, x8, x4
	madd x13, x11, x6, x13
	mul x16, x10, x4
	madd x6, x9, x6, x16
	mul x17, x8, x5
	madd x17, x11, x7, x17
	mul x16, x10, x5
	madd x7, x9, x7, x16
	orr x4, x13, x13
	orr x5, x17, x17
	movz x13, #32767, lsl #0
	and x8, x2, x13
	and x9, x3, x13
	movz x16, #32768, lsl #16
	add x8, x8, x16
	movz x16, #32768, lsl #32
	add x9, x9, x16
	movz x12, #1, lsl #0
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x1, #0, #0, ne
	csel x9, x11, x9, mi
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x1, #0, #0, ne
	csel x9, x11, x9, mi
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x1, #0, #0, ne
	csel x9, x11, x9, mi
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x1, #0, #0, ne
	csel x9, x11, x9, mi
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x1, #0, #0, ne
	csel x9, x11, x9, mi
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x1, #0, #0, ne
	csel x9, x11, x9, mi
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x1, #0, #0, ne
	csel x9, x11, x9, mi
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	movz x13, #16384, lsl #16
	movk x13, #8192, lsl #32
	movk x13, #8192, lsl #48
	movz x17, #16384, lsl #0
	add x8, x8, x13
	add x9, x9, x13
	lsr x11, x8, #47
	sub x11, x11, x17
	lsl x8, x8, #17
	lsr x8, x8, #48
	sub x8, x8, x17
	lsr x10, x9, #47
	sub x10, x10, x17
	lsl x9, x9, #17
	lsr x9, x9, #48
	sub x9, x9, x17
	mul x13, x8, x4
	madd x13, x11, x6, x13
	mul x16, x9, x4
	madd x6, x10, x6, x16
	mul x17, x8, x5
	madd x17, x11, x7, x17
	mul x16, x9, x5
	madd x7, x10, x7, x16
	orr x4, x13, x13
	orr x5, x17, x17
	movz x13, #0, lsl #0
	sub x1, x13, x1
	sub x1, x1, #1
	str x1, [x0, #480]
	movz x12, #0, lsl #0
	lsr x14, x4, #63
	sub x14, x12, x14
	eor x4, x4, x14
	sub x4, x4, x14
	lsr x15, x5, #63
	sub x15, x12, x15
	eor x5, x5, x15
	sub x5, x5, x15
	lsr x16, x6, #63
	sub x16, x12, x16
	eor x6, x6, x16
	sub x6, x6, x16
	lsr x17, x7, #63
	sub x17, x12, x17
	eor x7, x7, x17
	sub x7, x7, x17
	and x8, x4, x14
	and x9, x5, x15
	add x13, x8, x9
	and x8, x6, x16
	and x9, x7, x17
	add x11, x8, x9
	ldr x8, [x0, #192]
	eor x8, x8, x14
	mul x9, x8, x4
	umulh x10, x8, x4
	adds x1, x13, x9
	adc x2, x12, x10
	ldr x8, [x0, #224]
	eor x8, x8, x15
	mul x9, x8, x5
	umulh x10, x8, x5
	adds x1, x1, x9
	adc x2, x2, x10
	str x1, [x0, #320]
	ldr x8, [x0, #200]
	eor x8, x8, x14
	mul x9, x8, x4
	umulh x10, x8, x4
	adds x1, x2, x9
	adc x2, x12, x10
	ldr x8, [x0, #232]
	eor x8, x8, x15
	mul x9, x8, x5
	umulh x10, x8, x5
	adds x1, x1, x9
	adc x2, x2, x10
	str x1, [x0, #328]
	ldr x8, [x0, #208]
	eor x8, x8, x14
	mul x9, x8, x4
	umulh x10, x8, x4
	adds x1, x2, x9
	adc x2, x12, x10
	ldr x8, [x0, #240]
	eor x8, x8, x15
	mul x9, x8, x5
	umulh x10, x8, x5
	adds x1, x1, x9
	adc x2, x2, x10
	str x1, [x0, #336]
	ldr x8, [x0, #216]
	eor x8, x8, x14
	lsr x3, x8, #63
	sub x3, x12, x3
	and x3, x3, x4
	sub x3, x12, x3
	mul x9, x8, x4
	umulh x10, x8, x4
	adds x1, x2, x9
	adc x3, x3, x10
	ldr x8, [x0, #248]
	eor x8, x8, x15
	lsr x2, x8, #63
	sub x2, x12, x2
	and x2, x2, x5
	sub x2, x12, x2
	add x3, x3, x2
	mul x9, x8, x5
	umulh x10, x8, x5
	adds x1, x1, x9
	adc x3, x3, x10
	str x1, [x0, #344]
	str x3, [x0, #352]
	ldr x8, [x0, #192]
	eor x8, x8, x16
	mul x9, x8, x6
	umulh x10, x8, x6
	adds x1, x11, x9
	adc x2, x12, x10
	ldr x8, [x0, #224]
	eor x8, x8, x17
	mul x9, x8, x7
	umulh x10, x8, x7
	adds x1, x1, x9
	adc x2, x2, x10
	str x1, [x0, #360]
	ldr x8, [x0, #200]
	eor x8, x8, x16
	mul x9, x8, x6
	umulh x10, x8, x6
	adds x1, x2, x9
	adc x2, x12, x10
	ldr x8, [x0, #232]
	eor x8, x8, x17
	mul x9, x8, x7
	umulh x10, x8, x7
	adds x1, x1, x9
	adc x2, x2, x10
	str x1, [x0, #368]
	ldr x8, [x0, #208]
	eor x8, x8, x16
	mul x9, x8, x6
	umulh x10, x8, x6
	adds x1, x2, x9
	adc x2, x12, x10
	ldr x8, [x0, #240]
	eor x8, x8, x17
	mul x9, x8, x7
	umulh x10, x8, x7
	adds x1, x1, x9
	adc x2, x2, x10
	str x1, [x0, #376]
	ldr x8, [x0, #216]
	eor x8, x8, x16
	lsr x3, x8, #63
	sub x3, x12, x3
	and x3, x3, x6
	sub x3, x12, x3
	mul x9, x8, x6
	umulh x10, x8, x6
	adds x1, x2, x9
	adc x3, x3, x10
	ldr x8, [x0, #248]
	eor x8, x8, x17
	lsr x2, x8, #63
	sub x2, x12, x2
	and x2, x2, x7
	sub x2, x12, x2
	add x3, x3, x2
	mul x9, x8, x7
	umulh x10, x8, x7
	adds x1, x1, x9
	adc x3, x3, x10
	str x1, [x0, #384]
	str x3, [x0, #392]
	ldr x8, [x0, #256]
	eor x8, x8, x14
	mul x9, x8, x4
	umulh x10, x8, x4
	adds x1, x13, x9
	adc x2, x12, x10
	ldr x8, [x0, #288]
	eor x8, x8, x15
	mul x9, x8, x5
	umulh x10, x8, x5
	adds x1, x1, x9
	adc x2, x2, x10
	str x1, [x0, #400]
	ldr x8, [x0, #264]
	eor x8, x8, x14
	mul x9, x8, x4
	umulh x10, x8, x4
	adds x1, x2, x9
	adc x2, x12, x10
	ldr x8, [x0, #296]
	eor x8, x8, x15
	mul x9, x8, x5
	umulh x10, x8, x5
	adds x1, x1, x9
	adc x2, x2, x10
	str x1, [x0, #408]
	ldr x8, [x0, #272]
	eor x8, x8, x14
	mul x9, x8, x4
	umulh x10, x8, x4
	adds x1, x2, x9
	adc x2, x12, x10
	ldr x8, [x0, #304]
	eor x8, x8, x15
	mul x9, x8, x5
	umulh x10, x8, x5
	adds x1, x1, x9
	adc x2, x2, x10
	str x1, [x0, #416]
	ldr x8, [x0, #280]
	eor x8, x8, x14
	and x3, x14, x4
	sub x3, x12, x3
	mul x9, x8, x4
	umulh x10, x8, x4
	adds x1, x2, x9
	adc x3, x3, x10
	ldr x8, [x0, #312]
	eor x8, x8, x15
	and x2, x15, x5
	sub x2, x12, x2
	add x3, x3, x2
	mul x9, x8, x5
	umulh x10, x8, x5
	adds x1, x1, x9
	adc x3, x3, x10
	str x1, [x0, #424]
	str x3, [x0, #432]
	ldr x8, [x0, #256]
	eor x8, x8, x16
	mul x9, x8, x6
	umulh x10, x8, x6
	adds x1, x11, x9
	adc x2, x12, x10
	ldr x8, [x0, #288]
	eor x8, x8, x17
	mul x9, x8, x7
	umulh x10, x8, x7
	adds x1, x1, x9
	adc x2, x2, x10
	str x1, [x0, #440]
	ldr x8, [x0, #264]
	eor x8, x8, x16
	mul x9, x8, x6
	umulh x10, x8, x6
	adds x1, x2, x9
	adc x2, x12, x10
	ldr x8, [x0, #296]
	eor x8, x8, x17
	mul x9, x8, x7
	umulh x10, x8, x7
	adds x1, x1, x9
	adc x2, x2, x10
	str x1, [x0, #448]
	ldr x8, [x0, #272]
	eor x8, x8, x16
	mul x9, x8, x6
	umulh x10, x8, x6
	adds x1, x2, x9
	adc x2, x12, x10
	ldr x8, [x0, #304]
	eor x8, x8, x17
	mul x9, x8, x7
	umulh x10, x8, x7
	adds x1, x1, x9
	adc x2, x2, x10
	str x1, [x0, #456]
	ldr x8, [x0, #280]
	eor x8, x8, x16
	and x3, x16, x6
	sub x3, x12, x3
	mul x9, x8, x6
	umulh x10, x8, x6
	adds x1, x2, x9
	adc x3, x3, x10
	ldr x8, [x0, #312]
	eor x8, x8, x17
	and x2, x17, x7
	sub x2, x12, x2
	add x3, x3, x2
	mul x9, x8, x7
	umulh x10, x8, x7
	adds x1, x1, x9
	adc x3, x3, x10
	str x1, [x0, #464]
	str x3, [x0, #472]
	ldr x1, [x0, #320]
	ldr x2, [x0, #328]
	ldr x3, [x0, #336]
	ldr x8, [x0, #344]
	ldr x9, [x0, #352]
	extr x1, x2, x1, #59
	extr x2, x3, x2, #59
	extr x3, x8, x3, #59
	extr x8, x9, x8, #59
	str x1, [x0, #192]
	str x2, [x0, #200]
	str x3, [x0, #208]
	str x8, [x0, #216]
	ldr x1, [x0, #360]
	ldr x2, [x0, #368]
	ldr x3, [x0, #376]
	ldr x8, [x0, #384]
	ldr x9, [x0, #392]
	extr x1, x2, x1, #59
	extr x2, x3, x2, #59
	extr x3, x8, x3, #59
	extr x8, x9, x8, #59
	str x1, [x0, #224]
	str x2, [x0, #232]
	str x3, [x0, #240]
	str x8, [x0, #248]
	movz x13, #19, lsl #0
	ldr x1, [x0, #400]
	ldr x2, [x0, #408]
	ldr x3, [x0, #416]
	ldr x8, [x0, #424]
	ldr x9, [x0, #432]
	extr x10, x9, x8, #63
	lsr x11, x9, #63
	sub x10, x10, x11
	lsl x11, x10, #63
	add x8, x8, x11
	lsr x14, x10, #63
	sub x14, x12, x14
	mul x9, x10, x13
	umulh x11, x10, x13
	and x15, x14, x13
	sub x11, x11, x15
	adds x1, x1, x9
	adcs x2, x2, x11
	adcs x3, x3, x14
	adc x8, x8, x14
	str x1, [x0, #256]
	str x2, [x0, #264]
	str x3, [x0, #272]
	str x8, [x0, #280]
	ldr x1, [x0, #440]
	ldr x2, [x0, #448]
	ldr x3, [x0, #456]
	ldr x8, [x0, #464]
	ldr x9, [x0, #472]
	extr x10, x9, x8, #63
	lsr x11, x9, #63
	sub x10, x10, x11
	lsl x11, x10, #63
	add x8, x8, x11
	lsr x14, x10, #63
	sub x14, x12, x14
	mul x9, x10, x13
	umulh x11, x10, x13
	and x15, x14, x13
	sub x11, x11, x15
	adds x1, x1, x9
	adcs x2, x2, x11
	adcs x3, x3, x14
	adc x8, x8, x14
	str x1, [x0, #288]
	str x2, [x0, #296]
	str x3, [x0, #304]
	str x8, [x0, #312]
	sub x20, x20, #1
	cbnz x20, 22b
	movz x12, #0, lsl #0
	movz x6, #19, lsl #0
	movz x7, #65535, lsl #0
	movk x7, #65535, lsl #16
	movk x7, #65535, lsl #32
	movk x7, #32767, lsl #48
	ldr x2, [x0, #256]
	ldr x3, [x0, #264]
	ldr x4, [x0, #272]
	ldr x5, [x0, #280]
	lsr x8, x5, #63
	and x5, x5, x7
	mul x8, x8, x6
	adds x2, x2, x8
	adcs x3, x3, x12
	adcs x4, x4, x12
	adc x5, x5, x12
	movz x9, #65498, lsl #0
	movk x9, #65535, lsl #16
	movk x9, #65535, lsl #32
	movk x9, #65535, lsl #48
	movz x10, #65535, lsl #0
	movk x10, #65535, lsl #16
	movk x10, #65535, lsl #32
	movk x10, #65535, lsl #48
	subs x8, x9, x2
	sbcs x9, x10, x3
	sbcs x11, x10, x4
	sbc x10, x10, x5
	ldr x13, [x0, #216]
	lsr x13, x13, #63
	sub x13, x12, x13
	eor x8, x8, x2
	and x8, x8, x13
	eor x2, x2, x8
	eor x9, x9, x3
	and x9, x9, x13
	eor x3, x3, x9
	eor x11, x11, x4
	and x11, x11, x13
	eor x4, x4, x11
	eor x10, x10, x5
	and x10, x10, x13
	eor x5, x5, x10
	str x2, [x0, #544]
	str x3, [x0, #552]
	str x4, [x0, #560]
	str x5, [x0, #568]
	add x1, x19, #0
	movz w10, #0, lsl #0
	ldr x12, [x0, #544]
	ldr x13, [x0, #552]
	ldr x14, [x0, #560]
	ldr x15, [x0, #568]
	ldr x3, [x0, #64]
	mul x4, x3, x12
	mul x5, x3, x13
	mul x6, x3, x14
	mul x7, x3, x15
	umulh x2, x3, x12
	umulh x8, x3, x13
	umulh x9, x3, x14
	umulh x16, x3, x15
	adds x5, x5, x2
	adcs x6, x6, x8
	adcs x7, x7, x9
	adcs x21, x16, x10
	ldr x3, [x0, #72]
	mul x2, x3, x12
	mul x8, x3, x13
	mul x9, x3, x14
	mul x16, x3, x15
	adds x5, x5, x2
	adcs x6, x6, x8
	adcs x7, x7, x9
	adcs x21, x21, x16
	adcs x22, x10, x10
	umulh x2, x3, x12
	umulh x8, x3, x13
	umulh x9, x3, x14
	umulh x16, x3, x15
	adds x6, x6, x2
	adcs x7, x7, x8
	adcs x21, x21, x9
	adcs x22, x22, x16
	ldr x3, [x0, #80]
	mul x2, x3, x12
	mul x8, x3, x13
	mul x9, x3, x14
	mul x16, x3, x15
	adds x6, x6, x2
	adcs x7, x7, x8
	adcs x21, x21, x9
	adcs x22, x22, x16
	adcs x23, x10, x10
	umulh x2, x3, x12
	umulh x8, x3, x13
	umulh x9, x3, x14
	umulh x16, x3, x15
	adds x7, x7, x2
	adcs x21, x21, x8
	adcs x22, x22, x9
	adcs x23, x23, x16
	ldr x3, [x0, #88]
	mul x2, x3, x12
	mul x8, x3, x13
	mul x9, x3, x14
	mul x16, x3, x15
	adds x7, x7, x2
	adcs x21, x21, x8
	adcs x22, x22, x9
	adcs x23, x23, x16
	adcs x24, x10, x10
	umulh x2, x3, x12
	umulh x8, x3, x13
	umulh x9, x3, x14
	umulh x16, x3, x15
	adds x21, x21, x2
	adcs x22, x22, x8
	adcs x23, x23, x9
	adcs x24, x24, x16
	movz w11, #38, lsl #0
	mul x2, x11, x21
	adds x4, x4, x2
	mul x8, x11, x22
	adcs x5, x5, x8
	mul x9, x11, x23
	adcs x6, x6, x9
	mul x16, x11, x24
	adcs x7, x7, x16
	adcs x20, x10, x10
	umulh x2, x11, x21
	umulh x8, x11, x22
	umulh x9, x11, x23
	umulh x16, x11, x24
	adds x7, x7, x9
	adcs x20, x20, x16
	adds x16, x7, x7
	adc x9, x20, x20
	lsr x7, x16, #1
	movz w11, #19, lsl #0
	mul x9, x9, x11
	adds x4, x4, x9
	adcs x5, x5, x2
	adcs x6, x6, x8
	adcs x7, x7, x10
	str x4, [x0, #64]
	str x5, [x0, #72]
	str x6, [x0, #80]
	str x7, [x0, #88]
	movz w10, #0, lsl #0
	ldr x12, [x0, #544]
	ldr x13, [x0, #552]
	ldr x14, [x0, #560]
	ldr x15, [x0, #568]
	ldr x3, [x0, #96]
	mul x4, x3, x12
	mul x5, x3, x13
	mul x6, x3, x14
	mul x7, x3, x15
	umulh x2, x3, x12
	umulh x8, x3, x13
	umulh x9, x3, x14
	umulh x16, x3, x15
	adds x5, x5, x2
	adcs x6, x6, x8
	adcs x7, x7, x9
	adcs x21, x16, x10
	ldr x3, [x0, #104]
	mul x2, x3, x12
	mul x8, x3, x13
	mul x9, x3, x14
	mul x16, x3, x15
	adds x5, x5, x2
	adcs x6, x6, x8
	adcs x7, x7, x9
	adcs x21, x21, x16
	adcs x22, x10, x10
	umulh x2, x3, x12
	umulh x8, x3, x13
	umulh x9, x3, x14
	umulh x16, x3, x15
	adds x6, x6, x2
	adcs x7, x7, x8
	adcs x21, x21, x9
	adcs x22, x22, x16
	ldr x3, [x0, #112]
	mul x2, x3, x12
	mul x8, x3, x13
	mul x9, x3, x14
	mul x16, x3, x15
	adds x6, x6, x2
	adcs x7, x7, x8
	adcs x21, x21, x9
	adcs x22, x22, x16
	adcs x23, x10, x10
	umulh x2, x3, x12
	umulh x8, x3, x13
	umulh x9, x3, x14
	umulh x16, x3, x15
	adds x7, x7, x2
	adcs x21, x21, x8
	adcs x22, x22, x9
	adcs x23, x23, x16
	ldr x3, [x0, #120]
	mul x2, x3, x12
	mul x8, x3, x13
	mul x9, x3, x14
	mul x16, x3, x15
	adds x7, x7, x2
	adcs x21, x21, x8
	adcs x22, x22, x9
	adcs x23, x23, x16
	adcs x24, x10, x10
	umulh x2, x3, x12
	umulh x8, x3, x13
	umulh x9, x3, x14
	umulh x16, x3, x15
	adds x21, x21, x2
	adcs x22, x22, x8
	adcs x23, x23, x9
	adcs x24, x24, x16
	movz w11, #38, lsl #0
	mul x2, x11, x21
	adds x4, x4, x2
	mul x8, x11, x22
	adcs x5, x5, x8
	mul x9, x11, x23
	adcs x6, x6, x9
	mul x16, x11, x24
	adcs x7, x7, x16
	adcs x20, x10, x10
	umulh x2, x11, x21
	umulh x8, x11, x22
	umulh x9, x11, x23
	umulh x16, x11, x24
	adds x7, x7, x9
	adcs x20, x20, x16
	adds x16, x7, x7
	adc x9, x20, x20
	lsr x7, x16, #1
	movz w11, #19, lsl #0
	mul x9, x9, x11
	adds x4, x4, x9
	adcs x5, x5, x2
	adcs x6, x6, x8
	adcs x7, x7, x10
	str x4, [x0, #96]
	str x5, [x0, #104]
	str x6, [x0, #112]
	str x7, [x0, #120]
	movz w10, #0, lsl #0
	movz w11, #19, lsl #0
	movz x2, #65535, lsl #0
	movk x2, #65535, lsl #16
	movk x2, #65535, lsl #32
	movk x2, #32767, lsl #48
	ldr x4, [x0, #64]
	ldr x5, [x0, #72]
	ldr x6, [x0, #80]
	ldr x7, [x0, #88]
	lsr x8, x7, #63
	and x7, x7, x2
	mul x3, x8, x11
	adds x4, x4, x3
	adcs x5, x5, x10
	adcs x6, x6, x10
	adcs x7, x7, x10
	adds x21, x4, x11
	adcs x22, x5, x10
	adcs x23, x6, x10
	adcs x24, x7, x10
	lsr x8, x24, #63
	and x24, x24, x2
	sub x3, x10, x8
	eor x21, x21, x4
	and x21, x21, x3
	eor x4, x4, x21
	eor x22, x22, x5
	and x22, x22, x3
	eor x5, x5, x22
	eor x23, x23, x6
	and x23, x23, x3
	eor x6, x6, x23
	eor x24, x24, x7
	and x24, x24, x3
	eor x7, x7, x24
	add x2, x0, #0
	ldr x0, [x0, #48]
	ldr x19, [x2, #0]
	ldr x20, [x2, #8]
	ldr x21, [x2, #16]
	ldr x22, [x2, #24]
	ldr x23, [x2, #32]
	ldr x24, [x2, #40]
	str x4, [x0, #0]
	str x5, [x0, #8]
	str x6, [x0, #16]
	str x7, [x0, #24]
	ret
	.p2align 6
