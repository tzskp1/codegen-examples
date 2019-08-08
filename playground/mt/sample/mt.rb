W = 32
N = 634
M = 397
R = 31
U = 11
S = 7
T = 15
L = 18
A = 0x9908B0DF
B = 0x9D2C5680
C = 0xEFC60000

WHOLE_MASK = ("1" * W).to_i(2)
UPPER_MASK = ("1" * (W-R) + "0" * R).to_i(2)
LOWER_MASK = ("0" * (W-R) + "1" * R).to_i(2)

class MT
  def initialize(seed)
    @i = 0
    @x = [seed & WHOLE_MASK]

    1.upto(N-1) do |i|
      @x[i] = (1812433253 * (@x[i-1] ^ (@x[i-1] >> 30)) + i) & WHOLE_MASK
    end
    p @x
  end

  def next
    z = @x[@i] & UPPER_MASK | @x[(@i + 1) % N] & LOWER_MASK
    
    @x[@i] = @x[(@i + M) % N] ^ (z >> 1) ^ (z & 1 == 0 ? 0 : A)
    
    y = @x[@i]
    y = y ^ (y >> U)
    y = y ^ ((y << S) & B)
    y = y ^ ((y << T) & C)
    y = y ^ (y >> L)
  
    @i = (@i + 1) % N
    return y
  end
end

mt = MT.new(20150919)
2048.times do |i|
  print i, ": ", mt.next, "\n"
end

