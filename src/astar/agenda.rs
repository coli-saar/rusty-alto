pub(super) struct AstarAgenda {
    heap: Vec<(usize, f64)>,
    positions: Vec<usize>,
}

const NOT_IN_AGENDA: usize = usize::MAX;

pub(super) enum AgendaUpdate {
    Pushed,
    Updated,
}

impl Default for AstarAgenda {
    fn default() -> Self {
        Self::new()
    }
}

impl AstarAgenda {
    pub(super) fn new() -> Self {
        Self {
            heap: Vec::new(),
            positions: Vec::new(),
        }
    }

    fn ensure_position(&mut self, index: usize) {
        if self.positions.len() <= index {
            self.positions.resize(index + 1, NOT_IN_AGENDA);
        }
    }

    #[inline]
    fn parent(index: usize) -> usize {
        (index - 1) / 4
    }

    #[inline]
    fn first_child(index: usize) -> usize {
        index * 4 + 1
    }

    fn swap(&mut self, a: usize, b: usize) {
        self.heap.swap(a, b);
        self.positions[self.heap[a].0] = a;
        self.positions[self.heap[b].0] = b;
    }

    fn sift_up(&mut self, mut position: usize) {
        while position > 0 {
            let parent = Self::parent(position);
            if self.heap[parent].1 >= self.heap[position].1 {
                break;
            }
            self.swap(parent, position);
            position = parent;
        }
    }

    fn sift_down(&mut self, mut position: usize) {
        loop {
            let first = Self::first_child(position);
            if first >= self.heap.len() {
                break;
            }
            let end = (first + 4).min(self.heap.len());
            let mut best = first;
            for child in (first + 1)..end {
                if self.heap[child].1 > self.heap[best].1 {
                    best = child;
                }
            }
            if self.heap[position].1 >= self.heap[best].1 {
                break;
            }
            self.swap(position, best);
            position = best;
        }
    }

    pub(super) fn update_or_push(&mut self, index: usize, merit: f64) -> AgendaUpdate {
        self.ensure_position(index);
        let position = self.positions[index];
        if position == NOT_IN_AGENDA {
            let position = self.heap.len();
            self.heap.push((index, merit));
            self.positions[index] = position;
            self.sift_up(position);
            AgendaUpdate::Pushed
        } else {
            let old = self.heap[position].1;
            self.heap[position].1 = merit;
            if merit > old {
                self.sift_up(position);
            } else if merit < old {
                self.sift_down(position);
            }
            AgendaUpdate::Updated
        }
    }

    pub(super) fn pop(&mut self) -> Option<(usize, f64)> {
        let best = *self.heap.first()?;
        self.positions[best.0] = NOT_IN_AGENDA;
        let last = self.heap.pop().expect("heap was nonempty");
        if !self.heap.is_empty() {
            self.heap[0] = last;
            self.positions[last.0] = 0;
            self.sift_down(0);
        }
        Some(best)
    }

    pub(super) fn peek_merit(&self) -> Option<f64> {
        self.heap.first().map(|(_, merit)| *merit)
    }

    pub(super) fn len(&self) -> usize {
        self.heap.len()
    }

    pub(super) fn position_capacity(&self) -> usize {
        self.positions.len()
    }
}
