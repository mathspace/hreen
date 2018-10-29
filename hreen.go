package main

import (
	"fmt"
	"math/bits"
	"sort"
	"strconv"
	"strings"
	"sync"
)

// Width and height of the board
const BoardDim = 10

// Mask is a bitmask representing all cells on the board.
// LSB of the first byte is the top left corner cell and
// consequtive bits follow horizontally until the next
// y offset.
type Mask [2]uint64

// String represents the mask as string with '.' for empty
// and 'X' for occupied cells.
func (m Mask) String() string {
	b := strings.Builder{}
	for y := uint(0); y < BoardDim; y++ {
		for x := uint(0); x < BoardDim; x++ {
			v := m.At(x, y)
			if v == 0 {
				b.Write([]byte{'.'})
			} else {
				b.Write([]byte{'X'})
			}
		}
		b.Write([]byte{'\n'})
	}
	return b.String()
}

// Shadow returns a new mask with all the same occupied cells
// but with addition of all cells that share sides with the
// occupied cells.
func (m Mask) Shadow() Mask {
	s := Mask{}
	for y := uint(0); y < BoardDim; y++ {
		for x := uint(0); x < BoardDim; x++ {
			if m.At(x, y) == 1 || m.At(x-1, y) == 1 || m.At(x, y-1) == 1 || m.At(x+1, y) == 1 || m.At(x, y+1) == 1 {
				s = s.OrBitWith(x, y, 1)
			}
		}
	}
	return s
}

// Flipped returns a new mask that is a horizontal mirror of the
// original.
func (m Mask) Flipped() Mask {
	f := Mask{}
	for y := uint(0); y < BoardDim; y++ {
		for x := uint(0); x < BoardDim; x++ {
			f = f.OrBitWith(BoardDim-x-1, y, m.At(x, y))
		}
	}
	return f
}

// Rotated90 returns a new mask that is rotated 90 degrees clockwise.
func (m Mask) Rotated90() Mask {
	r := Mask{}
	for y := uint(0); y < BoardDim; y++ {
		for x := uint(0); x < BoardDim; x++ {
			r = r.OrBitWith(BoardDim-y-1, x, m.At(x, y))
		}
	}
	return r
}

// At returns the 1 if the cell at location x, y is occupied,
// otherwise 0. At accepts out of bound locations and returns 0.
func (m Mask) At(x, y uint) uint {
	if x < 0 || y < 0 || x >= BoardDim || y >= BoardDim {
		return 0
	}
	l := y*BoardDim + x
	return uint((m[l/64] >> (l % 64)) & 1)
}

// OrWith combines the current mask with 'o' mask to return
// a new mask whose each cell is the logical OR of the two
// masks.
func (m Mask) OrWith(o Mask) Mask {
	return Mask{m[0] | o[0], m[1] | o[1]}
}

// AndWith combines the current mask with 'o' mask to return
// a new mask whose each cell is the logical AND of the two
// masks.
func (m Mask) AndWith(o Mask) Mask {
	return Mask{m[0] & o[0], m[1] & o[1]}
}

// OrBitWith returns a new copy of the mask but with location
// x,y logically ORed with the given v.
func (m Mask) OrBitWith(x, y, v uint) Mask {
	n := m
	l := uint(y*BoardDim + x)
	n[l/64] |= uint64(v) << (l % 64)
	return n
}

// AndBitWith returns a new copy of the mask but with location
// x,y logically ANDed with the given v.
func (m Mask) AndBitWith(x, y, v uint) Mask {
	n := m
	l := uint(y*BoardDim + x)
	n[l/64] &= ^(uint64((^v)&1) << (l % 64))
	return n
}

// Zero returns true of no cells are occupied
func (m Mask) Zero() bool {
	return m[0]|m[1] == 0
}

// BitsSet returns the number of occupied cells.
func (m Mask) BitsSet() uint {
	return uint(bits.OnesCount64(m[0]) + bits.OnesCount64(m[1]))
}

// PieceMask represents a specific mask+shadow of a piece by its index
// into Piece.Masks and Piece.Shadows slices.
type PieceMask struct {
	Piece     *Piece
	MaskIndex int
}

// PieceChain represents an ordered set of pieces that make up a
// partial or a full solution.
type PieceChain []PieceMask

// String returns a string representation of a partial or a full
// solution in a two dimensional grid with each piece represented
// as a different letter.
func (c PieceChain) String() string {
	var b [BoardDim][BoardDim]byte
	for y := 0; y < BoardDim; y++ {
		for x := 0; x < BoardDim; x++ {
			b[y][x] = '.'
		}
	}
	for i, p := range c {
		for y := uint(0); y < BoardDim; y++ {
			for x := uint(0); x < BoardDim; x++ {
				if p.Piece.Masks[p.MaskIndex].At(x, y) == 1 {
					b[y][x] = []byte(string('A' + i))[0]
				}
			}
		}
	}
	str := strings.Builder{}
	for y := 0; y < BoardDim; y++ {
		str.Write(b[y][:])
		str.Write([]byte("\n"))
	}
	return str.String()
}

// Shadow returns a mask that is the bitwise OR of all the shadow
// masks in the chain.
func (c PieceChain) Shadow() Mask {
	s := Mask{}
	for _, p := range c {
		s = s.OrWith(p.Piece.Shadows[p.MaskIndex])
	}
	return s
}

// Piece represents a puzzle piece.
type Piece struct {
	Symbol  string
	Masks   []Mask
	Shadows []Mask
}

// NewPiece returns a new Piece with all its masks and shadows populated.
func NewPiece(symbol string, width uint, height uint, pmask uint64) *Piece {

	piece := Piece{
		Symbol: symbol,
	}

	// mask -> shadowMask map
	maskMap := map[Mask]Mask{}
	var masks []Mask

	for y := uint(0); y < BoardDim-height+1; y++ {
		for x := uint(0); x < BoardDim-width+1; x++ {
			m := Mask{}
			for iy := uint(0); iy < height; iy++ {
				for ix := uint(0); ix < width; ix++ {
					v := (pmask >> (iy*width + ix)) & 1
					m = m.OrBitWith(x+ix, y+iy, uint(v))
				}
			}
			masks = append(masks, m)
		}
	}

	for _, m := range masks {
		maskMap[m] = m.Shadow()
		m = m.Rotated90()
		maskMap[m] = m.Shadow()
		m = m.Rotated90()
		maskMap[m] = m.Shadow()
		m = m.Rotated90()
		maskMap[m] = m.Shadow()

		m = m.Rotated90()
		m = m.Flipped()
		maskMap[m] = m.Shadow()
		m = m.Rotated90()
		maskMap[m] = m.Shadow()
		m = m.Rotated90()
		maskMap[m] = m.Shadow()
		m = m.Rotated90()
		maskMap[m] = m.Shadow()
	}

	piece.Masks = make([]Mask, 0, len(maskMap))
	piece.Shadows = make([]Mask, 0, len(maskMap))

	for m, s := range maskMap {
		piece.Masks = append(piece.Masks, m)
		piece.Shadows = append(piece.Shadows, s)
	}

	return &piece
}

// play runs a depth first search of the search space and upon
// a solution, prints it out.
func play(pieces []*Piece, chain PieceChain) PieceChain {
	if len(pieces) == 0 {
		fmt.Println(" woohoo - we did it!!!!")
		fmt.Println(chain)
		return chain
	}
	piece := pieces[0]
	chainShadow := chain.Shadow()

	var pieceMasks []PieceMask
	for mi, m := range piece.Masks {
		if !chainShadow.AndWith(m).Zero() {
			continue
		}
		pieceMasks = append(pieceMasks, PieceMask{piece, mi})
	}
	sort.Slice(pieceMasks, func(i, j int) bool {
		imask := pieceMasks[i].Piece.Masks[pieceMasks[i].MaskIndex]
		jmask := pieceMasks[j].Piece.Masks[pieceMasks[j].MaskIndex]
		ibits := chainShadow.OrWith(imask).BitsSet()
		jbits := chainShadow.OrWith(jmask).BitsSet()
		return ibits < jbits
	})

	for _, pieceMask := range pieceMasks {
		nextChain := make([]PieceMask, len(chain)+1)
		copy(nextChain, chain)
		nextChain[len(chain)] = pieceMask
		if ret := play(pieces[1:], nextChain); ret != nil {
			return ret
		}
	}
	return nil
}

// linearPlay runs a single instances of play() at a time.
func linearPlay(pieces []*Piece) {
	if winningChain := play(pieces, []PieceMask{}); winningChain == nil {
		fmt.Println(" :( - we have a bug")
	}
}

// multiPlay runs all the top level play()s concurrently.
func multiPlay(pieces []*Piece) {
	fmt.Printf("%d top levels!\n", len(pieces[0].Masks))
	wg := sync.WaitGroup{}
	for i := range pieces[0].Masks {
		wg.Add(1)
		chain := []PieceMask{PieceMask{pieces[0], i}}
		go func(c PieceChain) {
			play(pieces[1:], c)
			wg.Done()
			fmt.Println("One top level done")
		}(chain)
	}
	wg.Wait()
}

func main() {

	// Setup pieces
	parseBinary := func(s string) uint64 {
		v, err := strconv.ParseUint(s, 2, 32)
		if err != nil {
			panic(err)
		}
		return v
	}

	pieces := []*Piece{
		NewPiece("+", 3, 3, parseBinary("010111010")),
		NewPiece("Z", 3, 3, parseBinary("110010011")),
		NewPiece("-L", 3, 3, parseBinary("010110011")),
		NewPiece("_L", 3, 3, parseBinary("010010111")),
		NewPiece("|", 1, 5, parseBinary("11111")),
		NewPiece("Li", 2, 3, parseBinary("101111")),
		NewPiece("|.", 2, 4, parseBinary("10101110")),
		NewPiece("L_", 3, 3, parseBinary("100100111")),
		NewPiece("C", 2, 3, parseBinary("111011")),
		NewPiece("M", 3, 3, parseBinary("110011001")),
		NewPiece("_S", 4, 2, parseBinary("00111110")),
		NewPiece("L", 2, 4, parseBinary("10101011")),
	}

	// Sort the pieces by largest average shadow descending
	sort.Slice(pieces, func(i, j int) bool {
		iBitsSum := float32(0)
		for _, s := range pieces[i].Shadows {
			iBitsSum += float32(s.BitsSet())
		}
		jBitsSum := float32(0)
		for _, s := range pieces[j].Shadows {
			jBitsSum += float32(s.BitsSet())
		}
		return jBitsSum/float32(len(pieces[j].Shadows)) < iBitsSum/float32(len(pieces[i].Shadows))
	})

	linearPlay(pieces)
	//multiPlay(pieces)

}
