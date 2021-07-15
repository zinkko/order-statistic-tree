
use super::*;

enum IterTask {
    Value(i32),
    Node(Box<Node>),
}

pub struct IntoIter {
    tasks: Vec<IterTask>,
}

fn add_tasks(tasks: &mut Vec<IterTask>, node: Box<Node>) {
    if let Some(right_node) = node.right {
        tasks.push(IterTask::Node(right_node));
    }
    tasks.push(IterTask::Value(node.value));
    if let Some(left_node) = node.left {
        tasks.push(IterTask::Node(left_node));
    }
}

impl IntoIter {
    pub fn new(tree: OrderStatTree) -> IntoIter {
        let mut tasks = Vec::new();
        if let Some(root_node) = tree.root {
            add_tasks(&mut tasks, root_node);
        }
        IntoIter { tasks: tasks }
    }
}

impl Iterator for IntoIter {
    type Item = i32;

    fn next(&mut self) -> Option<Self::Item> {
        while let Some(task) = self.tasks.pop() {
            match task {
                IterTask::Value(v) => return Some(v),
                IterTask::Node(node) => {
                    add_tasks(&mut self.tasks, node);
                }
            }
        }
        None
    }
}
