# inverse decimation method MT19937
W = 32
N = 624
M = 397
R = 31

P = W * N - R # 19937

UPPER_MASK = ("1" * (W-R) + "0" * R).to_i(2)
LOWER_MASK = ("0" * (W-R) + "1" * R).to_i(2)

BOTTOM_ZERO_MASK = ("1" * (W-1) + "0").to_i(2)
BOTTOM_ONE_MASK = 1

class MT
  def initialize(initial)
    @i = 0
    @x = initial
  end

  def next
    z = @x[@i] & UPPER_MASK | @x[(@i + 1) % N] & LOWER_MASK # computing (x^u_i | x^l_(i+1)) 
    
    y = @x[(@i + M) % N] ^ (z >> 1) ^ (z & 1 == 0 ? 0 : A) # multiplying A
    
    @x[@i] = y
    
    @i = (@i + 1) % N
    return y
  end
end

$timer = 0

def print_state(state)
  $timer = $timer + 1
  if $timer == 2 then
    N.times do |i|
      puts state[i]
    end
    exit
  end
end

def test_mt(a)
  x = []
  initial = []

  N.times do |i|
    x[i] = i
    initial[i] = x[i]
  end

  P.times do |i|
    print_state(x)
    mt = MT.new(x[0,N])
    (2*P-N).times {|i| x[N+i] = mt.next  } # generate
    1.upto(P) do |j|
      x[j] = x[2*j-1] # decimation
    end
    P.downto(N) do |k| # compute state
      y = x[k] ^ x[k - N + M] ^ (x[k-N+1] & 1 == 0 ? 0 : a)
      y = y << 1
      if x[k-N+1] & 1 == 0
        y = y & BOTTOM_ZERO_MASK
      else
        y = y | BOTTOM_ONE_MASK
      end
      x[k-N+1] = (UPPER_MASK & x[k-N+1] ) | (LOWER_MASK & y)
      x[k-N] = (UPPER_MASK & y) | (LOWER_MASK & x[k-N])
    end
  end

  if (x[0] & UPPER_MASK) != (initial[0] & UPPER_MASK)
    return false
  end

  1.upto(N-1) do |j|
    if initial[j] != x[j]
      return false
    end
  end
  true
end

A = 0x9908B0DF # the last row of the matrix A
A1 = 0x9908B0DD # the last row of the matrix A
 
if test_mt(A) 
  p "ok" 
else
  p "ng"
end  
