import java.io.FileOutputStream;
import java.io.IOException;
import java.io.OutputStream;
import java.util.Arrays;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.Set;

public class MainMT {

	/*
	 * In order to compute a term of size n of a Bonev sequence, I can simply
	 * imagine the term to be composed of two parts that have quite the same
	 * characteristics as my term.
	 * 
	 * The left sub-term starts with a 1 or a 2 and ends with a value of 1 or
	 * greater. I will chose the right sub-term to start at the same position
	 * where the left one ended That way my right sub-term will start with a
	 * value 1 or greater (same as the digit my left-term ended with) and end in
	 * a 1 or 2.
	 * 
	 * So in order to obtain all the terms of my sequence I will have to 1.
	 * calculate a suitable size for my left and right sub-terms (I have divided
	 * by two) 2. calculate all the possible values that the center digit can
	 * take 3. for each such center digit calculate all my left sub-terms ending
	 * in this digit 4. for each such center digit calculate all my right
	 * sub-terms starting in this digit 5. for each such center digit make the
	 * cartesian product among my left and right sub-terms
	 * 
	 * Note that, the concept of the term has to be slightly generalized
	 * allowing for terms to start with a positive number and end in another
	 * positive number; the Bonev terms being a subset of those.
	 * 
	 * Also, I felt the approach bottom-up could yield better results but I
	 * can't say for sure it really did. I realized kind of late in the
	 * development that most of the time (80%) is spent in allocating the needed
	 * memory. I tried circumventing the limitation by working on some parts
	 * while allocating memory for others but I was not successful so I went
	 * back to this, rather straightforward solution.
	 * 
	 * Memory issue apart, I tried fine graining the access so more threads
	 * could share one resource. This yielded some performance but as I said, it
	 * only aplies to the 20% of the overall execution time.
	 */

	class Sequence {

		/*
		 * This is the buffer keeping all the terms of this sequence. The terms
		 * are stacked one after the other starting at buffer[0] and position 0.
		 * A term will never be split between two buffers.
		 * 
		 * All terms have the same length so the n-the term of this sequence is
		 * found within buffers[n / bufferCount] at position termLength * (n %
		 * bufferCount).
		 */
		byte[][] buffers;

		/*
		 * Boundaries for the terms of the sequence. Notice that firstDigit and
		 * lastDigit can be any number and not just 1 or 2 (1 and 2 being
		 * ordinary cases). These are calculated during the initialization
		 * phase.
		 */
		int termLength, firstDigit, lastDigit;

		/*
		 * Number of terms in the sequence. Calculated during the initialization
		 * phase.
		 */
		long count;

		/*
		 * Each term of the sequence will be solved by merging a sub-term coming
		 * from a left sequence and a corresponding sub-term coming from the
		 * right sequence. All sub-terms coming from the left end with the same
		 * digit that right sub-terms start with. I have chosen to split the
		 * sequence right in the middle for best performance.
		 * 
		 * The two sequences (left and right) will overlap on the middle digit
		 * which will be taken out during the merge.
		 */
		Sequence[] leftSequences, rightSequences;

		/*
		 * For each leftSequence-rightSequence, its centerIndexes[] keeps the
		 * starting index inside this sequence.
		 */
		long[] centerIndexes;

		/*
		 * For each leftSequence-rightSequence, its centerCounts[] keeps number
		 * of the subterms.
		 */
		int[] centerCounts;

		int remainingMerges;

		/*
		 * This list is filled during the initialization phase and contains all
		 * the sequences that depend on this one to build their terms. During
		 * the calculation phase, when a term (or some terms) is calculated and
		 * stored in the buffer all the upSequence-s will be notified the fact.
		 * That way they can already start merging that as a sub-term in the
		 * predefined spot in their buffers.
		 * 
		 * When all the terms of this sequence have been calculated and stored
		 * in the buffer all the upSequences will be notified of the fact so
		 * they can check and propagate up the graph this same condition. Then
		 * we release all the references to the sequences down the graph
		 * (leftSequences[], rightSequences[]) in order to free memory.
		 * 
		 * If instead, we hit the memory threshold during this calculation (ex.
		 * buffer/buffers cannot be created) we indicate that there is nothing
		 * else that can be calculated by setting mainCountdownToCompletion to 0
		 * and return. It will be up to the getTerm(.) call to eventually find
		 * us or our sub-terms and re-stitch them together to obtain the term
		 * (aka. compressed)
		 */
		Set<Sequence> upSequences = new HashSet<Sequence>();

		/*
		 * The only constructor for a sequence, here it's done all calculating
		 * that can be done up front and needed by all the threads to run their
		 * jobs while being synchronized.
		 */
		public Sequence(int termLength, int firstDigit, int lastDigit, Sequence[][][] sequences) {
			sequences[termLength][firstDigit][lastDigit] = this;

			this.termLength = termLength;
			this.firstDigit = firstDigit;
			this.lastDigit = lastDigit;

			if (termLength < 3) {
				count = 1;
				buffers = new byte[][] { { (byte) firstDigit, (byte) lastDigit } };
			} else {
				int leftLength = termLength / 2 + 1;
				int rightLength = termLength - leftLength + 1;
				int minLeft = firstDigit - leftLength + 1;
				int maxLeft = firstDigit + leftLength; // -1 omitted
				int minRight = lastDigit - rightLength + 1;
				int maxRight = lastDigit + rightLength; // -1 omitted

				/*
				 * These two variables define the lowest (inclusive) and highest
				 * (exclusive) possible digit in the center axe. Makes no sense
				 * going beyond those values as a sequence cannot be obtained.
				 * Ex. for a sequence of termLength=5 with firstDigit=3 and
				 * lastDigit=2, centerMin will be 1 and centerMax will be 5 as
				 * in pic.
				 * 
				 * . 4 4 . . 3 3 3 3 . . 2 2 2 2 . . 1 1 . -----------------
				 * (fst) (ctr) (lst)
				 */

				int centerMin = minLeft > minRight ? minLeft : minRight;
				int centerMax = maxLeft < maxRight ? maxLeft : maxRight;
				if (centerMin < 1) {
					centerMin = 1;
				}

				remainingMerges = centerMax - centerMin;
				buffers = new byte[remainingMerges][];
				leftSequences = new Sequence[remainingMerges];
				rightSequences = new Sequence[remainingMerges];
				centerIndexes = new long[remainingMerges];
				centerCounts = new int[remainingMerges];

				for (int index = centerMin; index < centerMax; index++) {
					centerIndexes[index - centerMin] = count;

					Sequence leftSequence = sequences[leftLength][firstDigit][index];
					if (leftSequence == null) {
						leftSequences[index - centerMin] = leftSequence = sequences[leftLength][firstDigit][index] = new Sequence(
								leftLength, firstDigit, index, sequences);
					} else {
						leftSequences[index - centerMin] = leftSequence;
					}
					leftSequence.upSequences.add(this);

					Sequence rightSequence = sequences[rightLength][index][lastDigit];
					if (rightSequence == null) {
						rightSequences[index - centerMin] = rightSequence = sequences[rightLength][index][lastDigit] = new Sequence(
								rightLength, index, lastDigit, sequences);
					} else {
						rightSequences[index - centerMin] = rightSequence;
					}
					rightSequence.upSequences.add(this);

					centerCounts[index - centerMin] = (int) (leftSequence.count * rightSequence.count);
					count += centerCounts[index - centerMin];
				}
			}
		}

		/*
		 * This method simply counts and allocates the needed buffers to hold a
		 * certain sequence. If we run out of memory trying to allocate the
		 * buffers then we notify the fact by setting remainingSequences to 0,
		 * print a message and simply return; All the other threads will finish
		 * their current task and will notice that there is nothing else to do
		 * (since remainingSequences is 0) and simply return.
		 */
		private boolean allocateBuffers(int centerIndex) {
			synchronized (this) {
				if (buffers[centerIndex] == null) {
					try {
						buffers[centerIndex] = new byte[centerCounts[centerIndex] * termLength];
						return true;
					} catch (Throwable t) {
						// memory alert;
						// treating the condition outside this block
						// to avoid synchronization deadlocks
					}
				} else {
					return true;
				}
			}

			// let all the threads out!
			synchronized (queue) {
				if (remainingSequences != 0) {
					remainingSequences = 0;
					queue.notifyAll();
					System.out.println("!Insufficent memory!");
					System.out.println("Partial results are kept in the memory");
					System.out.println("serving as cache to calculate all the terms on demand");
					System.out.println();
				}

				return false;
			}
		}

		private void fill(byte[] src, int srcOffset, int srcLength, byte[] dst, int dstOffset, int dstLength) {
			if (srcLength < dstLength) {
				System.arraycopy(src, srcOffset, dst, dstOffset, srcLength);
				srcOffset = dstOffset;
				dstOffset += srcLength;
				dstLength -= srcLength;
			} else {
				System.arraycopy(src, srcOffset, dst, dstOffset, dstLength);
				return;
			}

			while (true) {
				if (srcLength < dstLength) {
					System.arraycopy(dst, srcOffset, dst, dstOffset, srcLength);
					dstOffset += srcLength;
					dstLength -= srcLength;
					srcLength <<= 1;
				} else {
					System.arraycopy(dst, srcOffset, dst, dstOffset, dstLength);
					break;
				}
			}
		}

		private void merge(byte[] subBuffer, int centerIndex, int offset) {
			if (!allocateBuffers(centerIndex)) {
				return;
			}

			Sequence subSequence = offset == 0 ? leftSequences[centerIndex] : rightSequences[centerIndex];
			int subStep = subSequence.termLength;
			byte[] buffer = buffers[centerIndex];

			synchronized (buffer) {
				if (buffer[0] != 0 || buffer[buffer.length - 1] != 0) {
					// buffer is dirty -- just copy
					for (int subOffset = 0; subOffset < subBuffer.length; subOffset += subStep, offset += termLength) {
						System.arraycopy(subBuffer, subOffset, buffer, offset, subStep);
					}

					leftSequences[centerIndex] = rightSequences[centerIndex] = null;

					// now buffer is fill and ready to be notified to parent
					for (Sequence upSequence : upSequences) {
						upSequence.notifySomeSubsequenceTermsAreReady(this, buffer);
					}

					synchronized (this) {
						if (--remainingMerges != 0) {
							return;
						}
					}

					// Is this one of the root elements?
					if (upSequences.isEmpty()) {
						synchronized (queue) {
							remainingSequences--;
							if (remainingSequences == 0)
								queue.notifyAll();
						}
					}
				} else {
					if (offset == 0) {
						int expandedLength = (int) (rightSequences[centerIndex].count * termLength);
						for (int subOffset = 0; subOffset < subBuffer.length; subOffset += subStep, offset += expandedLength) {
							fill(subBuffer, subOffset, subSequence.termLength, buffer, offset, expandedLength);
						}
					} else {
						for (int subOffset = 0; subOffset < subBuffer.length; subOffset += subStep, offset += termLength) {
							System.arraycopy(subBuffer, subOffset, buffer, offset, subStep);
						}

						offset -= subStep;
						if (leftSequences[centerIndex].count != 1)
							fill(buffer, 0, offset, buffer, offset, buffer.length - offset);
					}
				}
			}
		}

		// called by children on which we depend for solving our own terms
		private void notifySomeSubsequenceTermsAreReady(final Sequence subSequence, final byte[] subBuffer) {
			for (int cindex = 0; cindex < leftSequences.length; cindex++) {
				if (leftSequences[cindex] == subSequence) {
					final int ci = cindex;

					synchronized (queue) {
						if (termLength == 4 && firstDigit == 2 && lastDigit == 2)
							System.out.println("ML: " + subSequence.firstDigit + " " + subSequence.lastDigit + " " + ci);
						queue.add(new Runnable() {
							@Override
							public void run() {
								merge(subBuffer, ci, 0);
							}
						});

						queue.notifyAll();
					}
				}

				if (rightSequences[cindex] == subSequence) {
					final int ci = cindex;

					synchronized (queue) {
						if (termLength == 4 && firstDigit == 2 && lastDigit == 2)
							System.out.println("MR: " + subSequence.firstDigit + " " + subSequence.lastDigit + " " + ci);
						queue.add(new Runnable() {
							@Override
							public void run() {
								merge(subBuffer, ci, leftSequences[ci].termLength - 1);
							}
						});

						queue.notifyAll();
					}
				}
			}
		}

		/*
		 * This method will return the term directly from memory if it's in
		 * there. Otherwise it will decompress it by regenerating part of it.
		 */
		public byte[] getTerm(long index) {
			for (int ci = 1; ci < centerIndexes.length; ci++) {
				if (index < centerIndexes[ci]) {
					if (buffers[ci - 1] != null) {
						return Arrays.copyOfRange(buffers[ci - 1], (int) index, termLength);
					} else {
						byte[] term = new byte[termLength];
						byte[] left = leftSequences[ci - 1].getTerm(index);
						byte[] right = rightSequences[ci - 1].getTerm(index);
						System.arraycopy(left, 0, term, 0, left.length);
						System.arraycopy(right, 0, term, left.length - 1, right.length);
						return term;
					}
				} else if (index == centerIndexes[ci]) {
					return Arrays.copyOfRange(buffers[ci], 0, termLength);
				}
			}

			return null;
		}
	}

	// for private testing
	static final int THREAD_COUNT = 1;

	// marks the beginning of the tests
	long startTime;

	/*
	 * When this variable reaches 0 (or it's directly set to zero due to memory
	 * limits) threads won't pick up another tasks and will simply die.
	 */
	int remainingSequences;

	/*
	 * The task queue. Classic.
	 */
	LinkedList<Runnable> queue = new LinkedList<Runnable>();

	/*
	 * The sequences we are interested to calculate.
	 */
	Sequence[] sequencesToCalculate; // 1_1, 1_2, 2_1, 2_2

	public MainMT(int termLength, int threadCount) {
		if (termLength < 2) {
			throw new RuntimeException("Term length [" + termLength + "] is out of acceptable range.");
		}

		startTime = System.currentTimeMillis();
		int maxDigitPlus1 = (termLength + 5) / 2;
		Sequence[][][] sequences = new Sequence[termLength + 1][maxDigitPlus1][maxDigitPlus1];

		sequencesToCalculate = new Sequence[] { new Sequence(termLength, 1, 1, sequences),
				new Sequence(termLength, 1, 2, sequences), new Sequence(termLength, 2, 1, sequences),
				new Sequence(termLength, 2, 2, sequences), };

		// Sequences with termLength = 2 are calculated during the
		// initialization
		remainingSequences = termLength > 2 ? sequencesToCalculate.length : 0;

		// Spawning threads to process the chain
		for (int index = 0; index < threadCount - 1; index++) {
			new Thread() {
				public void run() {
					processChain();
				}
			}.start();
		}

		Sequence[][] level2 = sequences[2];
		for (int indexLeft = level2.length - 1; indexLeft > 0; indexLeft--) {
			for (int indexRight = level2[indexLeft].length - 1; indexRight > 0; indexRight--) {
				Sequence sequence = level2[indexLeft][indexRight];
				if (sequence != null) {
					for (Sequence upSequence : sequence.upSequences) {
						upSequence.notifySomeSubsequenceTermsAreReady(sequence, sequence.buffers[0]);
					}
				}
			}
		}

		System.out.println("Initialization phase finished [terms counted before being generated]");
		displayCounts();
	}

	/*
	 * Contains a loop where threads pick up tasks and execute them. They only
	 * leave the loop when the remainingSequences becomes 0.
	 */
	private void processChain() {
		Runnable task;

		while (true) {

			synchronized (queue) {

				try {
					task = queue.removeFirst();
				} catch (Exception e) {
					if (remainingSequences == 0) {
						break;
					}

					try {
						queue.wait();
					} catch (InterruptedException ie) {
					}

					continue;
				}
			}

			task.run();
		}
	}

	void displayCounts() {
		System.out.println("1_1 count: " + sequencesToCalculate[0].count);
		System.out.println("1_2 count: " + sequencesToCalculate[1].count);
		System.out.println("2_1 count: " + sequencesToCalculate[2].count);
		System.out.println("2_2 count: " + sequencesToCalculate[3].count);
		System.out
				.println("Total count: "
						+ (sequencesToCalculate[0].count + sequencesToCalculate[1].count + sequencesToCalculate[2].count + sequencesToCalculate[3].count));
		System.out.println();
	}

	void stopClockAndDisplayCounts() {
		System.out.println("Calculation phase finished [terms counted after being generated] in "
				+ (System.currentTimeMillis() - startTime) + " ms");
		displayCounts();
	}

	void writeResults(String fileName) {
		System.out.println("Writing results started");

		OutputStream os;
		byte[] newline = System.getProperty("line.separator").getBytes();

		try {
			os = new FileOutputStream(fileName);
		} catch (IOException oe) {
			System.err.println("Could not open the file");
			return;
		}

		try {
			for (int index = 0; index < 4; index++) {
				Sequence sequence = sequencesToCalculate[index];
				for (long index2 = 0; index2 < sequence.count; index2++) {
					byte[] term = sequence.getTerm(index2);
					for (int index3 = 0; index3 < term.length; index3++) {
						byte b = term[index3];
						term[index3] += b < 10 ? '0' : 'A' - 10;
					}
					os.write(term);
					os.write(newline);
				}
			}
		} catch (IOException oe) {
			System.err.println("Could not write to the file");
		} finally {
			try {
				os.close();
			} catch (IOException oe) {
				System.err.println("Could not close the file");
			}
		}

		System.out.println("Writing results finished");
	}

	public static void main(String[] args) {
		byte termLength;
		try {
			termLength = Byte.parseByte(args[0]);
		} catch (Exception e) {
			termLength = 2;
		}

		String fileName;
		try {
			fileName = args[1];
			if (fileName.equals("no")) {
				fileName = null;
			}
		} catch (Exception e) {
			fileName = null;
		}

		int threadCount;
		try {
			threadCount = Integer.parseInt(args[2]);
		} catch (Exception e) {
			threadCount = THREAD_COUNT;
		}

		// Initialize
		MainMT mainMT = new MainMT(termLength, threadCount);

		// Use main thread for computation as well
		mainMT.processChain();

		// Display counts and stop the clock
		mainMT.stopClockAndDisplayCounts();

		// Flush the results in the file
		if (fileName != null) {
			mainMT.writeResults(fileName);
		}

		// End
		System.out.println("Execution finished");
	}
}
