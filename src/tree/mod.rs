use std::fmt;

mod iter;
mod node;
mod utils;

use node::Node;
use utils::{Color, get_color, Direction, RotationType};



fn recursive_insert(node: &mut Node, value: i32) -> InsertReturn {
    let direction = if value < node.value { Direction::Left } else { Direction::Right };
    let uncle_color = get_color(node.get_child_as_ref(direction.opposite()));
    let mut next = node.get_child(direction);
    if next.is_none() {
        node.set_child(direction, Node::new(Color::Red, value));
        
        return match node.color {
            Color::Black => InsertReturn::Done,
            Color::Red => InsertReturn::Parent(direction),
        };
    }

    let state = recursive_insert(next.as_mut().unwrap(), value);
    match state {
        InsertReturn::Done => InsertReturn::Done,
        InsertReturn::Node => {
            if node.color == Color::Black {
                InsertReturn::Done
            } else {
                InsertReturn::Parent(direction)
            }
        },
        InsertReturn::Parent(child_direction) => {
            if uncle_color == Color::Red {
                next.unwrap().color = Color::Black;
                node.get_child(direction.opposite()).unwrap().color = Color::Black;
                node.color = Color::Red;
                InsertReturn::Node
            } else {
                // case 4 & 5, inner grandchild
                if child_direction != direction {
                    InsertReturn::Rotate(RotationType::Double(direction.opposite()))
                // case 5
                } else {
                    InsertReturn::Rotate(RotationType::Single(direction.opposite()))
                }
            }
        },
        InsertReturn::Rotate(rotation_type) => {
            let rotation_dir = rotation_type.get_direction();
            let child = *(node.remove_child(direction).take().unwrap());
            let mut rotated_node = child.rotate(rotation_type);
            rotated_node.color = Color::Black;
            rotated_node.get_child(rotation_dir).expect("The parent should have been rotated here").color = Color::Red;
            
            node.set_child(direction, rotated_node);
            InsertReturn::Done
        },
    }
}

fn recursive_delete(node: &mut Box<Node>, value: i32) -> DeleteReturn {
    if value == node.value {
        if node.left.is_some() && node.right.is_some() {
            let (delete_return, value) = successor_stage_delete(node.right.as_mut().unwrap());
            // successor value moved here, the successor node is deleted
            node.value = value;
            handle_delete_return(node, Direction::Right, delete_return)
        } else if node.color == Color::Red {
            DeleteReturn::Delete(None, true)
        } else if node.left.is_some() {
            DeleteReturn::Delete(node.left.take(), true)
        } else if node.right.is_some() {
            DeleteReturn::Delete(node.right.take(), true)
        } else {
            DeleteReturn::Delete(None, false)
        }
    } else if value < node.value {
        match node.left.as_mut() {
            Some(left_child) => {
                let delete_return = recursive_delete(left_child, value);
                handle_delete_return(node, Direction::Left, delete_return)
            },
            None => DeleteReturn::NotFound,
        }
    } else {
        match node.right.as_mut() {
            Some(right_child) => {
                let delete_return = recursive_delete(right_child, value);
                handle_delete_return(node, Direction::Right, delete_return)
            },
            None => DeleteReturn::NotFound,
        }
    }

}

fn successor_stage_delete(node: &mut Box<Node>) -> (DeleteReturn, i32) {
    match node.left.as_mut() {
        Some(left_child) => {
            let (delete_return, value) = successor_stage_delete(left_child);
            (handle_delete_return(node, Direction::Left, delete_return), value)
        },
        None => {
            let value = node.value;
            if node.color == Color::Red {
                (DeleteReturn::Delete(None, true), value)
            } else if node.right.is_some() {
                (DeleteReturn::Delete(node.right.take(), true), value)
            } else {
                (DeleteReturn::Delete(None, false), value)
            }
        }
    }
}

fn handle_delete_return(node: &mut Box<Node>, dir: Direction, state: DeleteReturn) -> DeleteReturn {
    match state {
        DeleteReturn::NotFound => DeleteReturn::NotFound,
        DeleteReturn::Done => DeleteReturn::Done,
        DeleteReturn::Continue => do_delete_checks(node, dir),
        DeleteReturn::Rotate(rotation_type) => {
            let child = node.remove_child(dir).unwrap();
            let old_parent_color = child.color;
            let mut rotated = child.rotate(rotation_type);
            rotated.color = old_parent_color;
            if let Some(ref mut left_node) = rotated.left {
                left_node.color = Color::Black;
            }
            if let Some(ref mut right_node) = rotated.right {
                right_node.color = Color::Black;
            }
            node.set_child(dir, rotated);
            DeleteReturn::Done
        },
        DeleteReturn::Delete(mut replacing_node, done) => {
            if let Some(ref mut node) = replacing_node {
                node.color = Color::Black;
            }
            node.set_child_or_leaf(dir, replacing_node);
            if done {
                DeleteReturn::Done
            } else {
                do_delete_checks(node, dir)
            }
        },
        DeleteReturn::Case3(direction) => {
            let child = *(node.remove_child(dir).unwrap());
            let rotated = case3(child, direction);
            node.set_child(dir, rotated);
            DeleteReturn::Done
        }
    }
}

fn case3(child: Node, direction: Direction) -> Node {
    let mut rotated = child.rotate(RotationType::Single(direction));
    rotated.color = Color::Black;
    rotated.get_child(direction).unwrap().color = Color::Red;
    let next_step = do_delete_checks(rotated.get_child(direction).unwrap(), direction);
    match next_step {
        DeleteReturn::Done => {},
        DeleteReturn::Rotate(second_rotation) => {
            let foobar = *(rotated.remove_child(direction).unwrap());
            let mut new_foo = foobar.rotate(second_rotation);
            // old parent color is red in this case
            new_foo.color = Color::Red;
            if let Some(ref mut left) = new_foo.left {
                left.color = Color::Black;
            }
            if let Some(ref mut right) = new_foo.right {
                right.color = Color::Black;
            }
            rotated.set_child(direction, new_foo);
        },
        _ => unreachable!("after case 3, the only remaining possible cases are 4, 5, and 6"),
    }
    rotated
}

fn do_delete_checks(parent: &mut Box<Node>, dir: Direction) -> DeleteReturn {
    let parent_is_black = parent.is_black();
    let node_is_black = get_color(parent.get_child_as_ref(dir)) == Color::Black;
    let sibling = parent.get_child(dir.opposite())
        .expect("Broken invariant: delete checks happen on the path up from a (former) black node. There can not be any leaves on such a path (except at the very end).");
    let sibling_is_black = sibling.is_black();
    
    let left_nephew_is_black = get_color(sibling.left.as_ref()) == Color::Black;
    let right_nephew_is_black = get_color(sibling.right.as_ref()) == Color::Black;
    let all_black = parent_is_black && node_is_black && sibling_is_black && left_nephew_is_black && right_nephew_is_black;
    // from siblings point of view. Sibling is on the opposite side
    let distant_nephew_is_red = match dir.opposite() {
        Direction::Left => !left_nephew_is_black,
        Direction::Right => !right_nephew_is_black,
    };

    if all_black {
        // case 1
        sibling.color = Color::Red;
        DeleteReturn::Continue
    } else if !sibling_is_black {
        // case 3
        DeleteReturn::Case3(dir)
    } else if !parent_is_black && sibling_is_black && left_nephew_is_black && right_nephew_is_black {
        // case 4
        sibling.color = Color::Red;
        parent.color = Color::Black;
        DeleteReturn::Done
    } else if distant_nephew_is_red {
        //case 6
        DeleteReturn::Rotate(RotationType::Single(dir))
    } else {
        // case 5 (+6)
        DeleteReturn::Rotate(RotationType::Double(dir))
    }
}

enum InsertReturn {
    Done,
    Node,
    Parent(Direction),
    Rotate(RotationType),
}

enum DeleteReturn {
    Done,
    NotFound,
    // Delete(possible replacement, checking done)
    Delete(Option<Box<Node>>, bool),
    Continue,
    Rotate(RotationType),
    Case3(Direction),
}

pub struct OrderStatTree {
    root: Option<Box<Node>>,
}

impl OrderStatTree {
    pub fn new() -> OrderStatTree {
        OrderStatTree { root: None }
    }

    pub fn is_empty(&self) -> bool {
        self.root.is_none()
    }

    pub fn contains(&self, value: i32) -> bool {
        let mut next = self.root.as_ref();
        while let Some(node) = next {
            if node.value == value {
                return true;
            } else if value < node.value {
                next = node.left.as_ref();
            } else {
                next = node.right.as_ref();
            }
        }
        false
    }

    pub fn insert(&mut self, value: i32) {
        if self.root.is_none() {
            self.root = Some(Box::new(Node {
                color: Color::Black,
                value: value,
                left: None,
                right: None,
            }));
            return;
        }
        let insert_result = recursive_insert(self.root.as_mut().unwrap(), value);
        match insert_result {
            InsertReturn::Done => {},
            InsertReturn::Node => {},
            InsertReturn::Parent(_) => {
                self.root.as_mut().unwrap().color = Color::Black;
            },
            InsertReturn::Rotate(rotation_type) => {
                let rotation_dir = rotation_type.get_direction();
                let old_root = *(self.root.take().unwrap());
                let mut new_root = old_root.rotate(rotation_type);
                new_root.color = Color::Black;
                new_root.get_child(rotation_dir).expect("The parent should have been rotated here").color = Color::Red;
                self.root = Some(Box::new(new_root));
            }
        }
    }

    pub fn delete(&mut self, value: i32) -> bool {
        if self.root.is_none() {
            return false;
        }
        let delete_result = recursive_delete(self.root.as_mut().unwrap(), value);
        match delete_result {
            DeleteReturn::Done => true,
            // case 2
            DeleteReturn::Continue => true,
            DeleteReturn::NotFound => false,
            DeleteReturn::Delete(replacement, _) => {
                self.root = replacement;
                true
            }
            DeleteReturn::Rotate(rotation_type) => {
                let old_root = self.root.take().unwrap();
                let old_parent_color = old_root.color;
                let mut new_root = old_root.rotate(rotation_type);
                new_root.color = old_parent_color;
                if let Some(ref mut left_child) = new_root.left {
                    left_child.color = Color::Black;
                }
                if let Some(ref mut right_child) = new_root.right {
                    right_child.color = Color::Black;
                }
                self.root = Some(Box::new(new_root));
                true
            },
            DeleteReturn::Case3(direction) => {
                let old_root = *(self.root.take().unwrap());
                let new_root = case3(old_root, direction);
                self.root = Some(Box::new(new_root));
                true
            }
        }
    }
}

impl IntoIterator for OrderStatTree {
    type Item = i32;
    type IntoIter = iter::IntoIter;

    fn into_iter(self) -> iter::IntoIter {
        iter::IntoIter::new(self)
    }
}

// helper function for fmt::Debug
fn fmt_subtree(node: &Box<Node>, formatter: &mut fmt::Formatter, indent: usize) -> fmt::Result {
    let indent_size = 2;
    formatter.write_fmt(format_args!("{:width$} {:?} {:?}\n", "", node.color, node.value, width=indent))?;

    if node.left.is_none() && node.right.is_none() {
        return Ok(());
    }

    match &node.left {
        Some(left_node) => fmt_subtree(left_node, formatter, indent + indent_size)?,
        None => formatter.write_fmt(format_args!("{:width$} Leaf\n", "", width=indent+indent_size))?,
    };
    match &node.right {
        Some(right_node) => fmt_subtree(right_node, formatter, indent + indent_size),
        None => formatter.write_fmt(format_args!("{:width$} Leaf\n", "", width=indent+indent_size)),
    }
}

impl fmt::Debug for OrderStatTree {
    fn fmt(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
        match &self.root {
            Some(root_node) => fmt_subtree(root_node, formatter, 0),
            None => formatter.write_str("Empty tree\n"),
        }
    }

}

#[cfg(test)]
mod tests {
    use super::*;

    mod tools {
        use super::super::*;

        pub fn assert_no_red_violations(tree: &OrderStatTree) {
            match &tree.root {
                Some(node) => check_red_violations(&node),
                None => {},
            }
        }

        fn check_red_violations(node: &Box<Node>) {
            if node.color == Color::Red {
                assert_eq!(get_color(node.left.as_ref()), Color::Black, "Child of red node must be black");
                assert_eq!(get_color(node.right.as_ref()), Color::Black, "Child of red node must be black");
            }

            if let Some(left_node) = node.left.as_ref() {
                check_red_violations(left_node);
            }
            if let Some(right_node) = node.right.as_ref() {
                check_red_violations(&right_node);
            }
        }

        pub fn assert_no_black_violations(tree: &OrderStatTree) {
            check_black_violations(tree.root.as_ref());
        }

        fn check_black_violations(node_or_leaf: Option<&Box<Node>>) -> i32 {
            if let Some(node) = node_or_leaf {
                let black_height_left = check_black_violations(node.left.as_ref());
                let black_height_right = check_black_violations(node.right.as_ref());
                
                assert_eq!(black_height_left, black_height_right, "Paths to leaves must contain same amount of black nodes. Violations in subtree of {:?} node with value {:?}", node.color, node.value);
                
                match node.color {
                    Color::Red => black_height_left,
                    Color::Black => black_height_left + 1,
                }
            } else {
                0
            }
        }

        pub fn assert_tree_size(tree: &OrderStatTree, expected_size: usize) {
            assert_eq!(subtree_size(tree.root.as_ref()), expected_size, "OrderStatTree was not the right size");
        }

        fn subtree_size(node_or_leaf: Option<&Box<Node>>) -> usize {
            match node_or_leaf {
                Some(node) => subtree_size(node.left.as_ref()) + subtree_size(node.right.as_ref()) + 1,
                None => 0,
            }
        }
    }

    #[test]
    fn test_new_tree_is_empty() {
        assert!(OrderStatTree::new().is_empty());
    }

    #[test]
    fn test_after_insert_tree_not_empty() {
        let mut tree = OrderStatTree::new();
        tree.insert(8);
        assert!(!tree.is_empty());
    }

    #[test]
    fn test_contains() {
        let t = OrderStatTree {
            root: Some(Box::new(Node {
                color: Color::Red,
                value: 5,
                left: Some(Box::new(Node {
                    color: Color::Red,
                    value: 3,
                    left: Some(Box::new(Node { color: Color::Red, value: 1, left: None, right: None })),
                    right: Some(Box::new(Node { color: Color::Red, value: 4, left: None, right: None })),
                })),
                right: Some(Box::new(Node {
                    color: Color::Red,
                    value: 8,
                    left: Some(Box::new(Node { color: Color::Red, value: 6, left: None, right: None})),
                    right: None,
                })),
            })),
        };
        assert!(t.contains(5));
        assert!(t.contains(6));
        assert!(t.contains(1));
        assert!(t.contains(4));

        assert!(!t.contains(2));
        assert!(!t.contains(7));
    }

    #[test]
    fn test_insert_1() {
        let mut t = OrderStatTree::new();
        t.insert(3);
        t.insert(6);
        t.insert(1);

        tools::assert_no_red_violations(&t);
        tools::assert_no_black_violations(&t);

        tools::assert_tree_size(&t, 3);
    }

    #[test]
    fn test_insert_2() {
        let mut tree = OrderStatTree::new();
        let values = vec![45, 13, 54, 14, 77, 12, 0, -3, 43, 111, 124, 55, 3, 1, 211434, 3];
        let expected_size = values.len();
        for i in values {
            tree.insert(i);
        }

        tools::assert_no_red_violations(&tree);
        tools::assert_no_black_violations(&tree);
        tools::assert_tree_size(&tree, expected_size);
    }

    #[test]
    fn test_into_iter() {
        let mut tree = OrderStatTree::new();
        let values = vec![145, -1243, 54, -123, 434, 13];
        for i in values {
            tree.insert(i);
        }

        assert_eq!(tree.into_iter().collect::<Vec<i32>>(), vec![-1243, -123, 13, 54, 145, 434]);
    }

    #[test]
    fn test_delete_1() {
        let mut tree = OrderStatTree::new();
        let initial_values = vec![176, 342, 941, 541, 973, 1234, 55, -1, 45, -2245, 451, 5];
        let initial_len = initial_values.len();
        for i in initial_values {
            tree.insert(i);
        }

        tree.delete(941);
        tree.delete(1234);
        tree.delete(-2245);
        tree.delete(-1);
        // not in tree!
        tree.delete(100);

        tools::assert_tree_size(&tree, initial_len - 4);
        tools::assert_no_red_violations(&tree);
        tools::assert_no_black_violations(&tree);
    }

    #[test]
    fn test_delete_2() {
        let mut tree = OrderStatTree::new();
        for i in 0..1000 {
            tree.insert(i);
        }

        tree.delete(645);
        tree.delete(646);
        tree.delete(87);
        
        tools::assert_tree_size(&tree, 997);
        tools::assert_no_red_violations(&tree);
        tools::assert_no_black_violations(&tree);
    }

    #[test]
    fn test_delete_3() {
        let mut tree = OrderStatTree::new();
        for i in 0..1000 {
            tree.insert(i % 5);
        }

        for _ in 0..10 {
            assert!(tree.delete(3));
        }

        tools::assert_tree_size(&tree, 990);
        tools::assert_no_red_violations(&tree);
        tools::assert_no_black_violations(&tree);
    }

    #[test]
    fn test_delete_all_then_insert() {
        let mut tree = OrderStatTree::new();
        assert!(!tree.delete(8));
        let v = vec![134, 75, 13, 54, 9, 134, 4];
        for i in v.iter() {
            tree.insert(*i);
        }

        for i in v.iter() {
            assert!(tree.delete(*i));
        }
        assert!(tree.is_empty());

        tree.insert(4);
        tree.insert(123);
        tree.insert(-1);

        tools::assert_tree_size(&tree, 3);
    }
}
