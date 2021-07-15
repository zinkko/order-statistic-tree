
use super::*;

pub struct Node {
    pub left: Option<Box<Node>>,
    pub right: Option<Box<Node>>,
    pub value: i32,
    pub color: Color,
    pub size: i32,
}

fn size(node_or_leaf: Option<&Box<Node>>) -> i32 {
    match node_or_leaf {
        Some(node) => node.size,
        None => 0,
    }
}

impl Node {
    pub fn new(color: Color, value: i32) -> Node {
        Node { color: color, value: value, left: None, right: None, size: 1 }
    }

    pub fn get_child(&mut self, dir: Direction) -> Option<&mut Box<Node>> {
        match dir {
            Direction::Left => self.left.as_mut(),
            Direction::Right => self.right.as_mut(),
        }
    }

    pub fn get_child_as_ref(&mut self, dir: Direction) -> Option<&Box<Node>> {
        match dir {
            Direction::Left => self.left.as_ref(),
            Direction::Right => self.right.as_ref(),
        }
    }

    pub fn set_child(&mut self, dir: Direction, node: Node) {
        match dir {
            Direction::Left => self.left = Some(Box::new(node)),
            Direction::Right => self.right = Some(Box::new(node)),
        };
        self.recalculate_size();
    }

    pub fn set_child_or_leaf(&mut self, dir: Direction, child: Option<Box<Node>>) {
        match dir {
            Direction::Left => self.left = child,
            Direction::Right => self.right = child,
        };
        self.recalculate_size();
    }

    pub fn remove_child(&mut self, dir: Direction) -> Option<Box<Node>> {
        let child = match dir {
            Direction::Left => {
                self.left.take()
            },
            Direction::Right => {
                self.right.take()
            }
        };
        self.recalculate_size();
        child
    }

    pub fn recalculate_size(&mut self) {
        self.size = 1 + size(self.left.as_ref()) + size(self.right.as_ref());
    }

    pub fn is_black(&self) -> bool {
        self.color == Color::Black
    }

    pub fn rotate(self, rtype: RotationType) -> Node {
        match rtype {
            RotationType::Single(dir) => self.rotate_once(dir),
            RotationType::Double(dir) => self.rotate_twice(dir),
        }
    }

    fn rotate_once(mut self, dir: Direction) -> Node {
        let mut new_g = self.clone();
        let u = self.remove_child(dir);
        let mut p = *(self.remove_child(dir.opposite()).expect("Rotation need one child"));
        let mut new_p = p.clone();
        let n = p.remove_child(dir.opposite());
        let s = p.remove_child(dir);

        new_g.set_child_or_leaf(dir, u);
        new_g.set_child_or_leaf(dir.opposite(), s);
        
        new_p.set_child(dir, new_g);
        new_p.set_child_or_leaf(dir.opposite(), n);

        new_p
    }

    fn rotate_twice(mut self, dir: Direction) -> Node {
        let mut new_g = self.clone();
        let u = self.remove_child(dir);
        let mut p = *(self.remove_child(dir.opposite()).expect("Double rotation needs the parent"));
        let mut new_p = p.clone();
        let mut n = *(p.remove_child(dir).expect("Double rotation needs inner grandchild"));
        let s = p.remove_child(dir.opposite());
        let mut new_n = n.clone();

        let b1 = n.remove_child(dir.opposite());
        let b2 = n.remove_child(dir);

        new_p.set_child_or_leaf(dir.opposite(), s);
        new_p.set_child_or_leaf(dir, b1);
        
        new_g.set_child_or_leaf(dir.opposite(), b2);
        new_g.set_child_or_leaf(dir, u);

        new_n.set_child(dir.opposite(), new_p);
        new_n.set_child(dir, new_g);

        new_n
    }
}

impl Clone for Node {
    fn clone(&self) -> Self {
        Node {
            color: self.color,
            value: self.value,
            size: self.size,
            // left and right are owned by self, so they cannot be moved here
            left: None,
            right: None,
        }
    }
}