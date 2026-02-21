package main

import (
	"bytes"
	"encoding/json"
	"fmt"
	"io"
	"log"
	"net/http"
	"os"
	"os/exec"
	"path/filepath"
	"strings"
	"sync"
	"time"
)

// FileNode represents a file or directory in the virtual filesystem
type FileNode struct {
	Name     string
	IsDir    bool
	Content  []byte
	Children map[string]*FileNode
	ModTime  time.Time
}

// Session represents a user session with its own filesystem
type Session struct {
	ID          string
	Root        *FileNode
	CurrentPath string
	LastAccess  time.Time
	mu          sync.RWMutex
}

// Global session storage
var (
	sessions   = make(map[string]*Session)
	sessionsMu sync.RWMutex
)

// Command request structure
type CommandRequest struct {
	Command string `json:"command"`
	Session string `json:"session"`
}

// Command response structure
type CommandResponse struct {
	Output   string `json:"output"`
	Error    bool   `json:"error"`
	Path     string `json:"path,omitempty"`
	Action   string `json:"action,omitempty"`
	Filename string `json:"filename,omitempty"`
	Content  string `json:"content,omitempty"`
	URL      string `json:"url,omitempty"`
}

// Save file request
type SaveRequest struct {
	Filename string `json:"filename"`
	Content  string `json:"content"`
	Session  string `json:"session"`
}

// NewFileNode creates a new file node
func NewFileNode(name string, isDir bool) *FileNode {
	node := &FileNode{
		Name:    name,
		IsDir:   isDir,
		ModTime: time.Now(),
	}
	if isDir {
		node.Children = make(map[string]*FileNode)
	}
	return node
}

// NewSession creates a new session with initialized filesystem
func NewSession(id string) *Session {
	root := NewFileNode("/", true)
	
	// Create initial directories
	home := NewFileNode("home", true)
	root.Children["home"] = home
	
	tmp := NewFileNode("tmp", true)
	root.Children["tmp"] = tmp
	
	return &Session{
		ID:          id,
		Root:        root,
		CurrentPath: "/home",
		LastAccess:  time.Now(),
	}
}

// GetSession retrieves or creates a session
func GetSession(sessionID string) *Session {
	sessionsMu.Lock()
	defer sessionsMu.Unlock()
	
	session, exists := sessions[sessionID]
	if !exists {
		session = NewSession(sessionID)
		sessions[sessionID] = session
	}
	
	session.LastAccess = time.Now()
	return session
}

// ResolvePath resolves a path relative to current directory
func (s *Session) ResolvePath(path string) string {
	if strings.HasPrefix(path, "/") {
		return filepath.Clean(path)
	}
	return filepath.Clean(filepath.Join(s.CurrentPath, path))
}

// GetNode retrieves a node at the given path
func (s *Session) GetNode(path string) *FileNode {
	if path == "/" {
		return s.Root
	}
	
	parts := strings.Split(strings.Trim(path, "/"), "/")
	current := s.Root
	
	for _, part := range parts {
		if part == "" {
			continue
		}
		if current.Children == nil {
			return nil
		}
		next, exists := current.Children[part]
		if !exists {
			return nil
		}
		current = next
	}
	
	return current
}

// CreateNode creates a new node at the given path
func (s *Session) CreateNode(path string, isDir bool) error {
	path = s.ResolvePath(path)
	dir := filepath.Dir(path)
	name := filepath.Base(path)
	
	parent := s.GetNode(dir)
	if parent == nil {
		return fmt.Errorf("parent directory does not exist: %s", dir)
	}
	
	if !parent.IsDir {
		return fmt.Errorf("parent is not a directory: %s", dir)
	}
	
	if _, exists := parent.Children[name]; exists {
		return fmt.Errorf("file or directory already exists: %s", name)
	}
	
	parent.Children[name] = NewFileNode(name, isDir)
	return nil
}

// DeleteNode removes a node at the given path
func (s *Session) DeleteNode(path string) error {
	path = s.ResolvePath(path)
	if path == "/" {
		return fmt.Errorf("cannot delete root directory")
	}
	
	dir := filepath.Dir(path)
	name := filepath.Base(path)
	
	parent := s.GetNode(dir)
	if parent == nil {
		return fmt.Errorf("parent directory does not exist")
	}
	
	if _, exists := parent.Children[name]; !exists {
		return fmt.Errorf("file or directory does not exist: %s", name)
	}
	
	delete(parent.Children, name)
	return nil
}

// ExecuteCommand processes and executes a command
func (s *Session) ExecuteCommand(cmd string) CommandResponse {
	s.mu.Lock()
	defer s.mu.Unlock()
	
	parts := strings.Fields(cmd)
	if len(parts) == 0 {
		return CommandResponse{Output: ""}
	}
	
	command := parts[0]
	args := parts[1:]
	
	switch command {
	case "help":
		return s.cmdHelp()
	case "ls":
		return s.cmdLs(args)
	case "pwd":
		return s.cmdPwd()
	case "cd":
		return s.cmdCd(args)
	case "mkdir":
		return s.cmdMkdir(args)
	case "touch":
		return s.cmdTouch(args)
	case "rm":
		return s.cmdRm(args)
	case "cat":
		return s.cmdCat(args)
	case "write", "edit":
		return s.cmdEdit(args)
	case "run":
		return s.cmdRun(args)
	case "serve":
		return s.cmdServe(args)
	case "clear":
		return CommandResponse{Output: ""}
	default:
		return CommandResponse{
			Output: fmt.Sprintf("Unknown command: %s. Type 'help' for available commands.", command),
			Error:  true,
		}
	}
}

func (s *Session) cmdHelp() CommandResponse {
	help := `Available Commands:
  help              Show this help message
  ls [dir]          List directory contents
  pwd               Print working directory
  cd <dir>          Change directory
  mkdir <dir>       Create directory
  touch <file>      Create empty file
  rm <file>         Remove file or directory
  cat <file>        Display file contents
  write <file>      Create/edit file in editor
  edit <file>       Edit existing file
  run python <file> Run Python script
  run node <file>   Run Node.js script
  serve <file.html> Preview HTML file
  clear             Clear terminal screen

Examples:
  mkdir myproject
  cd myproject
  touch index.html
  write index.html
  serve index.html`
	
	return CommandResponse{Output: help, Path: s.CurrentPath}
}

func (s *Session) cmdLs(args []string) CommandResponse {
	path := s.CurrentPath
	if len(args) > 0 {
		path = s.ResolvePath(args[0])
	}
	
	node := s.GetNode(path)
	if node == nil {
		return CommandResponse{
			Output: fmt.Sprintf("ls: cannot access '%s': No such file or directory", path),
			Error:  true,
		}
	}
	
	if !node.IsDir {
		return CommandResponse{
			Output: fmt.Sprintf("ls: %s: Not a directory", path),
			Error:  true,
		}
	}
	
	var output strings.Builder
	if len(node.Children) == 0 {
		return CommandResponse{Output: "", Path: s.CurrentPath}
	}
	
	for name, child := range node.Children {
		if child.IsDir {
			output.WriteString(fmt.Sprintf("%s/\n", name))
		} else {
			size := len(child.Content)
			output.WriteString(fmt.Sprintf("%s (%d bytes)\n", name, size))
		}
	}
	
	return CommandResponse{Output: strings.TrimSpace(output.String()), Path: s.CurrentPath}
}

func (s *Session) cmdPwd() CommandResponse {
	return CommandResponse{Output: s.CurrentPath, Path: s.CurrentPath}
}

func (s *Session) cmdCd(args []string) CommandResponse {
	if len(args) == 0 {
		s.CurrentPath = "/home"
		return CommandResponse{Output: "", Path: s.CurrentPath}
	}
	
	path := s.ResolvePath(args[0])
	node := s.GetNode(path)
	
	if node == nil {
		return CommandResponse{
			Output: fmt.Sprintf("cd: %s: No such file or directory", args[0]),
			Error:  true,
		}
	}
	
	if !node.IsDir {
		return CommandResponse{
			Output: fmt.Sprintf("cd: %s: Not a directory", args[0]),
			Error:  true,
		}
	}
	
	s.CurrentPath = path
	return CommandResponse{Output: "", Path: s.CurrentPath}
}

func (s *Session) cmdMkdir(args []string) CommandResponse {
	if len(args) == 0 {
		return CommandResponse{
			Output: "mkdir: missing operand",
			Error:  true,
		}
	}
	
	for _, dir := range args {
		err := s.CreateNode(dir, true)
		if err != nil {
			return CommandResponse{
				Output: fmt.Sprintf("mkdir: cannot create directory '%s': %v", dir, err),
				Error:  true,
			}
		}
	}
	
	return CommandResponse{Output: fmt.Sprintf("Created directory: %s", args[0]), Path: s.CurrentPath}
}

func (s *Session) cmdTouch(args []string) CommandResponse {
	if len(args) == 0 {
		return CommandResponse{
			Output: "touch: missing file operand",
			Error:  true,
		}
	}
	
	for _, file := range args {
		path := s.ResolvePath(file)
		node := s.GetNode(path)
		
		if node != nil {
			// File exists, update timestamp
			node.ModTime = time.Now()
		} else {
			// Create new file
			err := s.CreateNode(file, false)
			if err != nil {
				return CommandResponse{
					Output: fmt.Sprintf("touch: cannot create '%s': %v", file, err),
					Error:  true,
				}
			}
		}
	}
	
	return CommandResponse{Output: fmt.Sprintf("Created file: %s", args[0]), Path: s.CurrentPath}
}

func (s *Session) cmdRm(args []string) CommandResponse {
	if len(args) == 0 {
		return CommandResponse{
			Output: "rm: missing operand",
			Error:  true,
		}
	}
	
	for _, file := range args {
		err := s.DeleteNode(file)
		if err != nil {
			return CommandResponse{
				Output: fmt.Sprintf("rm: cannot remove '%s': %v", file, err),
				Error:  true,
			}
		}
	}
	
	return CommandResponse{Output: fmt.Sprintf("Removed: %s", args[0]), Path: s.CurrentPath}
}

func (s *Session) cmdCat(args []string) CommandResponse {
	if len(args) == 0 {
		return CommandResponse{
			Output: "cat: missing file operand",
			Error:  true,
		}
	}
	
	path := s.ResolvePath(args[0])
	node := s.GetNode(path)
	
	if node == nil {
		return CommandResponse{
			Output: fmt.Sprintf("cat: %s: No such file or directory", args[0]),
			Error:  true,
		}
	}
	
	if node.IsDir {
		return CommandResponse{
			Output: fmt.Sprintf("cat: %s: Is a directory", args[0]),
			Error:  true,
		}
	}
	
	return CommandResponse{Output: string(node.Content), Path: s.CurrentPath}
}

func (s *Session) cmdEdit(args []string) CommandResponse {
	if len(args) == 0 {
		return CommandResponse{
			Output: "edit: missing file operand",
			Error:  true,
		}
	}
	
	filename := args[0]
	path := s.ResolvePath(filename)
	node := s.GetNode(path)
	
	var content string
	if node != nil {
		if node.IsDir {
			return CommandResponse{
				Output: fmt.Sprintf("edit: %s: Is a directory", filename),
				Error:  true,
			}
		}
		content = string(node.Content)
	} else {
		// Create new file
		err := s.CreateNode(filename, false)
		if err != nil {
			return CommandResponse{
				Output: fmt.Sprintf("edit: cannot create '%s': %v", filename, err),
				Error:  true,
			}
		}
	}
	
	return CommandResponse{
		Action:   "edit",
		Filename: filename,
		Content:  content,
		Path:     s.CurrentPath,
	}
}

func (s *Session) cmdRun(args []string) CommandResponse {
	if len(args) < 2 {
		return CommandResponse{
			Output: "run: usage: run <python|node> <file>",
			Error:  true,
		}
	}
	
	runtime := args[0]
	filename := args[1]
	
	path := s.ResolvePath(filename)
	node := s.GetNode(path)
	
	if node == nil {
		return CommandResponse{
			Output: fmt.Sprintf("run: %s: No such file", filename),
			Error:  true,
		}
	}
	
	if node.IsDir {
		return CommandResponse{
			Output: fmt.Sprintf("run: %s: Is a directory", filename),
			Error:  true,
		}
	}
	
	var cmd *exec.Cmd
	var cmdName string
	
	switch runtime {
	case "python", "python3":
		cmdName = "python3"
		cmd = exec.Command(cmdName, "-c", string(node.Content))
	case "node", "nodejs":
		cmdName = "node"
		cmd = exec.Command(cmdName, "-e", string(node.Content))
	default:
		return CommandResponse{
			Output: fmt.Sprintf("run: unsupported runtime: %s (use 'python' or 'node')", runtime),
			Error:  true,
		}
	}
	
	// Check if runtime exists
	_, err := exec.LookPath(cmdName)
	if err != nil {
		return CommandResponse{
			Output: fmt.Sprintf("run: %s is not installed or not in PATH", cmdName),
			Error:  true,
		}
	}
	
	var stdout, stderr bytes.Buffer
	cmd.Stdout = &stdout
	cmd.Stderr = &stderr
	
	err = cmd.Run()
	
	output := stdout.String()
	if stderr.Len() > 0 {
		output += stderr.String()
	}
	
	if err != nil {
		return CommandResponse{
			Output: fmt.Sprintf("Error executing %s:\n%s", filename, output),
			Error:  true,
		}
	}
	
	if output == "" {
		output = fmt.Sprintf("Executed %s successfully (no output)", filename)
	}
	
	return CommandResponse{Output: output, Path: s.CurrentPath}
}

func (s *Session) cmdServe(args []string) CommandResponse {
	if len(args) == 0 {
		return CommandResponse{
			Output: "serve: missing file operand",
			Error:  true,
		}
	}
	
	filename := args[0]
	path := s.ResolvePath(filename)
	node := s.GetNode(path)
	
	if node == nil {
		return CommandResponse{
			Output: fmt.Sprintf("serve: %s: No such file", filename),
			Error:  true,
		}
	}
	
	if node.IsDir {
		return CommandResponse{
			Output: fmt.Sprintf("serve: %s: Is a directory", filename),
			Error:  true,
		}
	}
	
	return CommandResponse{
		Action:   "preview",
		Filename: filename,
		URL:      "/preview/" + filename,
		Path:     s.CurrentPath,
	}
}

// SaveFile saves content to a file
func (s *Session) SaveFile(filename, content string) error {
	s.mu.Lock()
	defer s.mu.Unlock()
	
	path := s.ResolvePath(filename)
	node := s.GetNode(path)
	
	if node == nil {
		return fmt.Errorf("file does not exist: %s", filename)
	}
	
	if node.IsDir {
		return fmt.Errorf("is a directory: %s", filename)
	}
	
	node.Content = []byte(content)
	node.ModTime = time.Now()
	
	return nil
}

// HTTP Handlers
func handleExecute(w http.ResponseWriter, r *http.Request) {
	if r.Method != http.MethodPost {
		http.Error(w, "Method not allowed", http.StatusMethodNotAllowed)
		return
	}
	
	var req CommandRequest
	if err := json.NewDecoder(r.Body).Decode(&req); err != nil {
		http.Error(w, err.Error(), http.StatusBadRequest)
		return
	}
	
	session := GetSession(req.Session)
	response := session.ExecuteCommand(req.Command)
	
	w.Header().Set("Content-Type", "application/json")
	json.NewEncoder(w).Encode(response)
}

func handleSave(w http.ResponseWriter, r *http.Request) {
	if r.Method != http.MethodPost {
		http.Error(w, "Method not allowed", http.StatusMethodNotAllowed)
		return
	}
	
	var req SaveRequest
	if err := json.NewDecoder(r.Body).Decode(&req); err != nil {
		http.Error(w, err.Error(), http.StatusBadRequest)
		return
	}
	
	session := GetSession(req.Session)
	err := session.SaveFile(req.Filename, req.Content)
	
	var response CommandResponse
	if err != nil {
		response = CommandResponse{
			Output: err.Error(),
			Error:  true,
		}
	} else {
		response = CommandResponse{
			Output: "File saved successfully",
			Path:   session.CurrentPath,
		}
	}
	
	w.Header().Set("Content-Type", "application/json")
	json.NewEncoder(w).Encode(response)
}

func handlePreview(w http.ResponseWriter, r *http.Request) {
	sessionID := r.URL.Query().Get("session")
	if sessionID == "" {
		http.Error(w, "Missing session ID", http.StatusBadRequest)
		return
	}
	
	session := GetSession(sessionID)
	session.mu.RLock()
	defer session.mu.RUnlock()
	
	// Extract filename from path
	filename := strings.TrimPrefix(r.URL.Path, "/preview/")
	if filename == "" {
		http.Error(w, "Missing filename", http.StatusBadRequest)
		return
	}
	
	path := session.ResolvePath(filename)
	node := session.GetNode(path)
	
	if node == nil {
		http.Error(w, "File not found", http.StatusNotFound)
		return
	}
	
	if node.IsDir {
		http.Error(w, "Is a directory", http.StatusBadRequest)
		return
	}
	
	// Determine content type
	contentType := "text/html"
	if strings.HasSuffix(filename, ".css") {
		contentType = "text/css"
	} else if strings.HasSuffix(filename, ".js") {
		contentType = "application/javascript"
	} else if strings.HasSuffix(filename, ".json") {
		contentType = "application/json"
	}
	
	w.Header().Set("Content-Type", contentType)
	w.Write(node.Content)
}

func handleIndex(w http.ResponseWriter, r *http.Request) {
	if r.URL.Path != "/" {
		http.NotFound(w, r)
		return
	}
	
	indexHTML, err := os.ReadFile("index.html")
	if err != nil {
		http.Error(w, "Could not read index.html", http.StatusInternalServerError)
		return
	}
	
	w.Header().Set("Content-Type", "text/html")
	w.Write(indexHTML)
}

func cleanupSessions() {
	ticker := time.NewTicker(5 * time.Minute)
	defer ticker.Stop()
	
	for range ticker.C {
		sessionsMu.Lock()
		now := time.Now()
		for id, session := range sessions {
			if now.Sub(session.LastAccess) > 30*time.Minute {
				delete(sessions, id)
			}
		}
		sessionsMu.Unlock()
	}
}

func main() {
	// Start session cleanup goroutine
	go cleanupSessions()
	
	http.HandleFunc("/", handleIndex)
	http.HandleFunc("/execute", handleExecute)
	http.HandleFunc("/save", handleSave)
	http.HandleFunc("/preview/", handlePreview)
	
	port := os.Getenv("PORT")
	if port == "" {
		port = "8080"
	}
	
	fmt.Printf("\n🚀 EXGit Terminal Server Started\n")
	fmt.Printf("📡 Listening on http://localhost:%s\n", port)
	fmt.Printf("✨ Open this URL in your browser to access the terminal\n\n")
	
	if err := http.ListenAndServe(":"+port, nil); err != nil {
		log.Fatal(err)
	}
}
